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
  ppTerm,
} from "./join.js";
import { assert, KeyedMap, ArrayMap } from "./collections.js";

function tup(tag, values, weight) {
  return [tag].concat(weight ? values.concat([weight]) : values);
}
function evalQuery({ db, js }, query, context = [emptyBinding()]) {
  // redundant. done to ensure result does not contain any input context
  if (query.length === 0) return context.map((c) => c.clone());

  return query.reduce(joinBindings, context);

  function* readDb(c, values) {
    // todo!
    for (let [tuple, _] of db.entries()) {
      yield tuple;
    }
  }

  function* joinBindings(context, tuple) {
    let tg = tag(tuple);
    let ts = terms(tuple);
    for (let c of context) {
      let values = ts.map((t) => evalTerm(js, c, t));
      for (let tuple of readDb(c, values)) {
        if (tupleValid(tuple, tg, values)) {
          yield extendBinding(c, tuple, values);
        }
      }
    }
  }

  function tupleValid(tuple, tag, values) {
    function tval(i) {
      return tuple[i + 1];
    }

    assert(Array.isArray(values));
    if (tuple[0] !== tag) return false;
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
  return new KeyedMap(key, [[tuple, true]]);
}

/* Datalog evaluation state:
 *   dbAtoms: maps (tuple -> {(binding, weight)}),
 *   dbAggregates: maps (tuple -> weight)
 * Atoms from the former are aggregated into the latter.
 * Queries produce atoms but see aggregates.
 */
function mkProgram(rules, js, relationTypes) {
  return {
    rules,
    js,
    relationTypes,
  };
}

function emptyState() {
  return {
    dbAtoms: new ArrayMap(new KeyedMap(key)),
    dbAggregates: new KeyedMap(key),
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
  return rules.map(({ head, body }) => ({
    head: flatten(head),
    body: flatten(body),
    id: uniqueInt(),
  }));
}

function seminaive(program, state, worklist, init = true) {
  let { rules, relationTypes, js } = program;
  let { dbAtoms, dbAggregates } = state;
  let dependencies = new ArrayMap(new KeyedMap(key));
  let debug = false;

  // Rules with empty LHS
  if (init) assertEmptyTuple();
  // Rules with LHS
  while (worklist.length > 0) {
    let tuple = worklist.pop();
    log("pop tuple: ", ppTuple(tuple));
    assertTuple(tuple);
  }

  /* Definitions */

  function log(...args) {
    if (debug) console.log(...args);
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
        let context = evalQuery({ db: singletonDb(tuple), js }, [spot], [emptyBinding()]);
        // solve remaining query
        for (let binding of evalQuery({ db: dbAggregates, js }, rest, context)) {
          assertBinding({ rule, binding }, binding.notes.get("used"));
        }
      }
    }
    // insert tuple
    dbAggregates.set(tuple, true);
  }

  function assertBinding(x, used) {
    log("assertBinding: ", x, used);
    for (let key of used) {
      log("asserting used: ", ppTuple(key));
      dependencies.add(key, x);
      log(dependencies.get(key));
    }
    changeBinding(x, "add");
  }

  function changeBinding({ rule, binding }, mod) {
    for (let terms of rule.head) {
      changeAtom(substitute(js, binding, terms), rule.id, binding, mod);
    }
  }
  function changeAtom(atom, id, binding, mod) {
    let oldWeighted = getWeight(core(atom));
    switch (mod) {
      case "add":
        insertAtom(dbAtoms, atom, id, binding);
        break;
      case "del":
        removeAtom(dbAtoms, atom, id, binding);
        break;
      default:
        throw "";
    }
    let newWeighted = getWeight(core(atom));
    // todo: batching
    if (!tupleEqual(weight(oldWeighted), weight(newWeighted))) {
      retractTuple(oldWeighted);
      let { zero } = reductionType(tag(atom));
      if (!valEqual(weight(newWeighted), zero)) queueTuple(newWeighted);
    } else {
      log("no change: ", oldWeighted, newWeighted);
    }
  }

  function getWeight(core) {
    let { zero, add } = reductionType(tag(core));
    let weight = dbAtoms.get(core).reduce((acc, { weight }) => add(acc, weight), zero);
    return core.concat([weight]);
  }
  function reductionType(tag) {
    function wrap(type, fn) {
      return ({ value: a }, { value: b }) => type(fn(a, b));
    }
    let semirings = {
      bool: { type: mkInt, add: wrap(mkInt, (a, b) => a || b), zero: mkInt(0) },
      min: { type: mkInt, add: wrap(mkInt, Math.min), zero: mkInt(Infinity) },
      max: { type: mkInt, add: wrap(mkInt, Math.max), zero: mkInt(-Infinity) },
      num: { type: mkInt, add: wrap(mkInt, (a, b) => a + b), zero: mkInt(0) },
    };
    let ty = relationTypes[tag] || "bool";
    assert(ty);
    assert(ty in semirings);
    return semirings[ty];
  }
  function queueTuple(tuple) {
    log("queueTuple: ", ppTuple(tuple)); //tuple.map(ppTerm).join(","));
    worklist = [tuple].concat(worklist);
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
    for (let ruleBinding of depends(tuple)) {
      log("retractBinding: ", ruleBinding);
      retractBinding(ruleBinding);
    }
    worklist = worklist.filter((t) => !tupleEqual(t, tuple));
    dbAggregates.delete(tuple);
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
    for (let i = 0; i < body.length; i++) {
      if (tag(body[i]) === t) yield { spot: body[i], rest: removeAt(body, i) };
    }
  }
  return null;
}

function substituteTerm(js, binding, term) {
  if (isLiteral(term)) return evalTerm(js, binding, term);
  if (isHole(term)) {
    return freshId();
  } else {
    assert(isVar(term));
    let v = term.value;
    let maybeV = binding.get(v);
    if (maybeV) return maybeV;
    else {
      let id = freshId();
      binding.set(v, id);
      return id;
    }
  }
}

function substitute(js, binding, terms) {
  return terms.map((v, i) => (i > 0 ? substituteTerm(js, binding, v) : v));
}

export { fixRules, emptyState, mkProgram, seminaive };
