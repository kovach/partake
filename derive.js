// TODO: match zero
import {
  emptyBinding,
  evalTerm,
  uniqueInt,
  isLiteral,
  freshId,
  isVar,
  isHole,
  valEqual,
  mkInt,
  mkBox,
  ppTerm,
} from "./join.js";
import { assert, range, KeyedMap, ArrayMap } from "./collections.js";

function tup(tag, values, weight) {
  return [tag].concat(weight ? values.concat([weight]) : values);
}
function reductionType(relationTypes, tag) {
  return relationTypes[tag] || "bool";
}

function reductionOps(relationTypes, tag) {
  function wrap(type, fn) {
    return ({ value: a }, { value: b }) => type(fn(a, b));
  }
  let semirings = {
    bool: { type: mkInt, add: wrap(mkInt, (a, b) => a || b), zero: mkInt(0) },
    min: { type: mkInt, add: wrap(mkInt, Math.min), zero: mkInt(Infinity) },
    max: { type: mkInt, add: wrap(mkInt, Math.max), zero: mkInt(-Infinity) },
    num: { type: mkInt, add: wrap(mkInt, (a, b) => a + b), zero: mkInt(0) },
    last: { type: mkBox, add: wrap(mkBox, (_a, b) => b), zero: mkBox(null) },
  };
  let ty = reductionType(relationTypes, tag);
  assert(ty);
  assert(ty in semirings);
  return semirings[ty];
}

function evalQuery({ db, js, relationTypes }, query, context = [emptyBinding()]) {
  // redundant. done to ensure result does not contain any input context
  //if (query.length === 0) return context.map((c) => c.clone());
  if (query.length === 0) return context.map((c) => c.clone());

  return query.reduce(joinBindings, context);

  function* readDb(tag, c, values) {
    let extern = tag[0] === "@";
    if (extern) {
      for (let x of js[tag.slice(1)](...values)) {
        yield [tag, ...x];
      }
    } else {
      for (let [core, weight] of db.entries()) {
        yield [...core, weight];
      }
    }
  }

  function getOrInsertZero(tag, values) {
    // weird format
    let c = [tag, ...core(values)];
    let w = weight(values); // w = zero
    if (db.contains(c)) {
      return [...c, db.get(c)];
    }
    db.set(c, w);
    return [...c, w];
  }

  function* joinBindings(context, pattern) {
    let tg = tag(pattern);
    let ts = terms(pattern);
    for (let c of context) {
      let values = ts.map((t) => evalTerm(js, c, t));
      let zero = reductionOps(relationTypes, tg).zero;
      if (valEqual(weight(values), zero)) {
        // Negation case
        for (let v of values) {
          // todo: ideally want to warn here instead
          // currently this line can be reached when we try to unify a new positive tuple against a negative pattern
          //assert(!isVar(v), "negated pattern must not contain unbound variables");
          if (isVar(v)) return;
        }
        let tuple = getOrInsertZero(tg, values);
        if (valEqual(weight(tuple), zero)) yield extendBinding(c, tuple, values);
      } else {
        // Normal case
        for (let tuple of readDb(tg, c, values)) {
          if (tupleValid(tuple, tg, values)) {
            yield extendBinding(c, tuple, values);
          }
        }
      }
    }
  }

  function tupleValid(tuple, tag, values) {
    function tval(i) {
      return tuple[i + 1];
    }

    assert(Array.isArray(values));
    if (tuple[0] !== tag) {
      return false;
    }
    if (values.length !== tuple.length - 1) return false;
    // all tuple components match the pattern where it is already bound (a literal)
    return values.every((term, index) => {
      return !(isLiteral(term) && !valEqual(term, tval(index)));
    });
  }

  function extendBinding(c, tuple, values) {
    function tval(i) {
      return tuple[i + 1];
    }

    c = c.clone();
    values.forEach((term, index) => {
      if (isVar(term)) c.set(term.value, tval(index));
    });
    c.notes.add("used", tuple);
    return c;
  }
}

// todo
function key(tuple) {
  return JSON.stringify(tuple);
}
function singletonDb(tuple) {
  return new KeyedMap(key, [[core(tuple), weight(tuple)]]);
}

function mkProgram(rules, js, relationTypes) {
  return {
    rules,
    js,
    relationTypes,
  };
}

/* Datalog evaluation state:
 *   dbAtoms: maps (tuple -> {(binding, weight)}),
 *   dbAggregates: maps (tuple -> weight)
 * Atoms from the former are aggregated into the latter.
 * Queries produce atoms but see aggregates.
 */
function emptyState() {
  return {
    dbAtoms: new ArrayMap(new KeyedMap(key)),
    dbAggregates: new KeyedMap(key),
    addWorklist: [],
    delWorklist: [],
    init: true,
    dependencies: new ArrayMap(new KeyedMap(key)),
  };
}

// tuple accessor functions
function tag(tuple) {
  return tuple[0];
}
function terms(tuple) {
  return tuple.slice(1, tuple.length);
}
function core(tuple) {
  return tuple.slice(0, tuple.length - 1);
}
function weight(tuple) {
  return tuple[tuple.length - 1];
}

function ppTuple(tuple) {
  return `(${tag(tuple)} ${terms(tuple).map(ppTerm).join(" ")})`;
}

function fixRules(rules) {
  function flatten(q) {
    return q.map(({ tag, terms }) => [tag].concat(terms));
  }
  return rules.map(({ head, body, type }) => ({
    body: flatten(body),
    head: type === "command" ? head : flatten(head),
    id: uniqueInt(),
    type,
  }));
}

let mod = {
  add: "add",
  del: "del",
  cases: (val, add, del) => {
    switch (val) {
      case "add":
        return add();
      case "del":
        return del();
      default:
        throw "mod";
    }
  },
};

/* Main logic: iteratively derive and aggregate implications of `program.rules`.
 * mutates state
 */
function seminaive(executionContext) {
  let { program, state } = executionContext;
  let { rules, relationTypes, js } = program;
  let { dependencies, dbAtoms, dbAggregates, init } = state;
  // !!! TODO
  //let dependencies = new ArrayMap(new KeyedMap(key));
  let debug = 0;

  if (init) {
    // Rules with empty LHS
    assertEmptyTuple();
    state.init = false;
  }
  // Rules with LHS
  while (state.addWorklist.length + state.delWorklist.length > 0) {
    if (state.delWorklist.length > 0) {
      let tuple = state.delWorklist.pop();
      log("pop del tuple: ", ppTuple(tuple), tuple);
      retractTuple(tuple);
    } else {
      let tuple = state.addWorklist.pop();
      log("pop add tuple: ", ppTuple(tuple), tuple);
      assertTuple(tuple);
    }
  }
  return null;

  /* Definitions */

  function log(...args) {
    if (debug > 1) console.log(...args);
  }

  function log2(...args) {
    if (debug > 0) console.log(...args);
  }

  function assertEmptyTuple() {
    for (let rule of rules) {
      if (rule.body.length === 0) {
        assertBinding({ rule, binding: emptyBinding() }, []);
      }
    }
  }
  function assertTuple(tuple) {
    for (let rule of rules) {
      for (let { spot, rest } of splitRule(rule.body, tag(tuple))) {
        // bind new tuple
        let context = evalQuery(
          { db: singletonDb(tuple), js, relationTypes },
          [spot],
          [emptyBinding()]
        );
        // solve remaining query
        for (let binding of evalQuery(
          { db: dbAggregates, js, relationTypes },
          rest,
          context
        )) {
          assertBinding({ rule, binding }, binding.notes.get("used"));
        }
      }
    }
    // insert tuple
    dbAggregates.set(core(tuple), weight(tuple));
  }

  function assertBinding(x, used) {
    log("assertBinding: ", x, used);
    assert(x.rule.type);
    if (x.rule.type === "dyn") {
      for (let key of used) {
        log("asserting used: ", ppTuple(key));
        dependencies.add(key, x);
        log("dependency list: ", dependencies.get(key));
      }
    }
    changeBinding(x, "add");
  }

  function changeBinding({ rule, binding }, mod) {
    switch (rule.type) {
      case "dyn":
        for (let terms of rule.head) {
          changeAtom(substitute(js, binding, terms), rule.id, binding, mod);
        }
        break;
      case "imp":
        for (let terms of rule.head) {
          changeAtom(
            substitute(js, binding, terms, (allowFresh = true)),
            rule.id,
            binding,
            mod
          );
        }
        break;
      case "command":
        evalTerm(js, binding, rule.head);
        break;
    }
  }
  function changeAtom(atom, id, binding, m) {
    let oldWeighted = getWeight(core(atom));
    mod.cases(
      m,
      () => insertAtom(dbAtoms, atom, id, binding),
      () => removeAtom(dbAtoms, atom, id, binding)
    );
    let newWeighted = getWeight(core(atom));
    // todo: batching
    if (!valEqual(weight(oldWeighted), weight(newWeighted))) {
      //if (!tupleEqual(weight(oldWeighted), weight(newWeighted))) {
      queueTupleDel(oldWeighted);
      let { zero } = reductionOps(relationTypes, tag(atom));
      if (!valEqual(weight(newWeighted), zero)) queueTupleAdd(newWeighted);
    } else {
      log("no change: ", oldWeighted, newWeighted);
    }
  }

  function getWeight(core) {
    let { zero, add } = reductionOps(relationTypes, tag(core));
    let values = dbAtoms.get(core);
    let weight = values.reduce((acc, { weight }) => add(acc, weight), zero);
    if (values.length > 2) {
      //console.log("\n\nasdf ", values);
      //console.log("asdf ", weight.value);
    }
    return core.concat([weight]);
  }
  // actually makes worklist into a stack
  function queueTupleAdd(tuple) {
    log("queueTupleAdd: ", ppTuple(tuple));
    //worklist = [{ tuple, mod: mod.add }].concat(worklist);
    state.addWorklist.push(tuple);
  }
  function queueTupleDel(tuple) {
    log("queueTupleDel: ", ppTuple(tuple));
    //worklist = [{ tuple, mod: mod.add }].concat(worklist);
    state.delWorklist.push(tuple);
  }
  function bindingEq(b1, b2) {
    return b1.eq(b2, valEqual);
  }
  function insertAtom(db, atom, id, binding) {
    if (!containsAtom(db, atom, id, binding))
      db.add(core(atom), { id, binding, weight: weight(atom) });
  }
  function containsAtom(db, atom, id, binding) {
    return db
      .get(core(atom))
      .some(({ id: i, binding: b }) => i === id && bindingEq(b, binding));
  }
  function removeAtom(db, atom, id, binding) {
    db.update(core(atom), (arr) =>
      arr.filter(({ id: i, binding: b }) => i !== id || !bindingEq(b, binding))
    );
  }
  function tupleEqual(t1, t2) {
    return JSON.stringify(t1) === JSON.stringify(t2);
  }
  function retractTuple(tuple) {
    log("retractTuple: ", ppTuple(tuple));
    for (let ruleBinding of dependencies.get(tuple)) {
      log("retractBinding: ", ruleBinding);
      retractBinding(ruleBinding);
    }
    dependencies.reset(tuple);
    state.addWorklist = state.addWorklist.filter((t) => !tupleEqual(t, tuple));
    dbAggregates.delete(core(tuple));
  }
  function retractBinding(x) {
    changeBinding(x, "del");
  }
  function depends(tuple) {
    return dependencies.get(tuple);
  }

  function* splitRule(body, t) {
    function removeAt(array, i) {
      return array.filter((_, j) => j !== i);
    }
    // if a query contains a `!predicate ...` pattern, then we *only* produce spots at
    // any patterns starting with `!`
    let hasBang = (pattern) => pattern[0][0] === "!";
    let indices = range(body.length);
    if (body.some(hasBang)) indices = indices.filter((i) => hasBang(body[i]));
    let removeBang = (p) => (hasBang(p) ? [p[0].slice(1), ...p.slice(1)] : p);
    body = body.map(removeBang);
    for (let i of indices) {
      if (tag(body[i]) === t) yield { spot: body[i], rest: removeAt(body, i) };
    }
  }
}

function substituteTerm(js, binding, term, allowFresh) {
  if (isLiteral(term)) return evalTerm(js, binding, term);
  // todo: check during parsing
  assert(isVar(term));
  let v = term.value;
  let result = binding.get(v);
  if (result) return result;
  if (!allowFresh) assert(false, "dynamic rule not allowed to generate fresh values");
  result = freshId();
  if (isHole(term)) return result;
  binding.set(v, result);
  return result;
}

function substitute(js, binding, terms, allowFresh = false) {
  return terms.map((v, i) => (i > 0 ? substituteTerm(js, binding, v, allowFresh) : v));
}

// External interface to add/remove boolean state tuples
function addTuple(state, tuple) {
  //console.log("extern add: ", tuple);
  tuple = tuple.concat(mkInt(1));
  state.addWorklist.push(tuple);
}
function delTuple(state, tuple) {
  tuple = tuple.concat(mkInt(1));
  state.delWorklist.push(tuple);
}

export {
  fixRules,
  emptyState,
  mkProgram,
  evalQuery,
  seminaive,
  substitute,
  addTuple,
  delTuple,
  reductionType,
  core,
  weight,
};
