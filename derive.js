// TODO: match zero
import {
  af,
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
  isSym,
  Binding,
} from "./join.js";
import { assert, range, KeyedMap, ArrayMap, MonoidMap } from "./collections.js";
import { dotExpandQuery } from "./parse.js";

class DB {
  constructor(tuples = []) {
    this.value = new MonoidMap(
      () => new KeyedMap(key),
      () => {
        throw "";
      }
    );
    for (let t of tuples) {
      this.addTuple(t);
    }
  }
  addTuple(tuple) {
    this.value.get(tag(tuple)).set(core(tuple), weight(tuple));
  }
  addCW(c, w) {
    this.value.get(tag(c)).set(c, w);
  }
  remove(c) {
    this.value.get(tag(c)).delete(c);
  }
  has(core) {
    return this.value.get(tag(core)).contains(core);
  }
  weight(core) {
    return this.value.get(tag(core)).get(core);
  }
  *all() {
    for (let db of this.value.map.values()) {
      yield* db.entries();
    }
  }
  *ofTag(tag) {
    yield* this.value.get(tag).entries();
  }
  size() {
    return af(this.value.map.values())
      .map((m) => m.map.size)
      .sum();
  }
}

let _true = mkInt(1);

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
    last: { type: mkBox, add: (_a, b) => b, zero: mkBox(null) },
  };
  let ty = reductionType(relationTypes, tag);
  assert(ty);
  assert(ty in semirings);
  return semirings[ty];
}

function evalQuery(
  { location, db, js, relationTypes },
  query,
  context = [emptyBinding()]
) {
  // redundant. done to ensure result does not contain any input context
  if (query.length === 0) return context.map((c) => c.clone());

  return query.reduce(joinBindings, context);

  // todo: need tag type abstraction
  function* readDb(t, binding, values) {
    let marker = t[0];
    switch (marker) {
      case "@":
        for (let x of js[t.slice(1)](...values)) {
          yield [t, ...x];
        }
        break;
      case "*":
        for (let [core, weight] of db.ofTag(t)) {
          let t2 = tag(core);
          if (t === t2) {
            assert(location);
            let [_tag, id_, ...vals] = [...core, weight];
            if (valEqual(id_, location)) {
              let result = [_tag, ...vals];
              yield result;
            } else {
            }
          }
        }
        break;
      case "^":
        let rel = binding.get(t.slice(1));
        assert(isSym(rel));
        for (let [[_t, ...vals], weight] of db.ofTag(rel.value)) {
          yield [t, ...vals, weight];
        }
        break;
      default:
        for (let [core, weight] of db.ofTag(t)) {
          yield [...core, weight];
        }
        break;
    }
  }

  function getOrInsertZero(tag, values) {
    // weird format
    let c = [tag, ...core(values)];
    let w = weight(values); // w = zero
    if (db.has(c)) {
      return [...c, db.weight(c)];
    }
    db.addCW(c, w);
    return [...c, w];
  }

  function* joinBindings(context, pattern) {
    let tg = tag(pattern);
    let ts = terms(pattern);
    for (let binding of context) {
      let values = ts.map((t) => evalTerm(js, binding, t));
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
        if (valEqual(weight(tuple), zero)) yield extendBinding(binding, tuple, values);
      } else {
        // Normal case
        for (let tuple of readDb(tg, binding, values)) {
          if (tupleValid(tuple, tg, values)) {
            yield extendBinding(binding, tuple, values);
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
Array.prototype.key = function () {
  if (this._key) return this._key;
  this._key = JSON.stringify(this);
  return this._key;
};

function key(tuple) {
  return tuple.key();
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
    dbAggregates: new DB(),
    addWorklist: [],
    delWorklist: [],
    atomWorklist: [],
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

function fixQuery(q) {
  let { prefix, query } = dotExpandQuery(q);
  q = [...prefix, ...query];
  q = q.map(({ tag, terms }) => [tag].concat(terms));
  return q;
}
function fixRules(rules) {
  return rules.map(({ head, body, type }) => ({
    body: fixQuery(body),
    head: type === "command" ? head : fixQuery(head),
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
function mkSeminaive(r, js, relationTypes) {
  let rules = [...r];
  let state = emptyState();
  let { dependencies, dbAtoms, dbAggregates, init } = state;
  let debug = 0;

  let obj = {};
  obj.defs = { js, relationTypes };
  obj.atoms = dbAtoms;
  obj.init = () => {
    assert(init, "call init once (todo fix)");
    if (init) {
      // Rules with empty LHS
      assertEmptyTuple();
      state.init = false;
    }
  };
  obj.query = (query, context = emptyBinding()) => {
    return af(evalQuery({ db: dbAggregates, js, relationTypes }, query, [context]));
  };
  obj.hasWork = () => {
    return (
      state.addWorklist.length || state.delWorklist.length || state.atomWorklist.length
    );
  };
  let _nullBinding = new Binding();
  obj.solve = () => {
    // Rules with LHS
    while (obj.hasWork()) {
      if (state.atomWorklist.length > 0) {
        for (let a of state.atomWorklist) {
          changeAtom(a, `${uniqueInt()}`, _nullBinding, mod.add);
        }
        state.atomWorklist = [];
      } else if (state.delWorklist.length > 0) {
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
  };

  obj.addRules = (rs) => {
    // find all result bindings from just new rule; no fixpoint
    assertEmptyTuple(rs);
    if (rs.some((r) => r.body.length > 0)) {
      for (let [c, w] of dbAggregates.all()) {
        assertTuple([...c, w], rs);
      }
    }
    // add rule and solve
    rs.forEach((r) => rules.push(r));
    obj.solve();
  };
  obj.getState = () => {
    return state;
  };
  obj.print = (filter = []) => {
    //let tupleCmp = (a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b));
    let excluded = 0;
    function pp(ps) {
      return (
        ps
          //.sort(tupleCmp)
          .map(([tag, ...terms]) => {
            if (filter.includes(tag)) {
              excluded++;
              return "";
            }
            // TODO: factor out and reuse
            let ty = reductionType(relationTypes, tag);
            if (ty === "bool") {
              if (valEqual(weight(terms), _true)) {
                return [tag].concat(core(terms).map(ppTerm)).join(" ");
              } else {
                return [tag, ...core(terms).map(ppTerm), "->", "false"].join(" ");
              }
            } else {
              return [tag, ...core(terms).map(ppTerm), "->", ppTerm(weight(terms))].join(
                " "
              );
            }
          })
          .filter((l) => l.length > 0)
          .sort()
          .join("\n")
      );
    }
    console.log(pp(af(dbAggregates.all()).map(([core, w]) => [...core, w])));
    console.log("hidden tuple count: ", excluded);
  };

  return obj;

  function log(...args) {
    if (debug > 1) console.log(...args);
  }

  function log2(...args) {
    if (debug > 0) console.log(...args);
  }

  function assertEmptyTuple(theRules = rules) {
    for (let rule of theRules) {
      if (rule.body.length === 0) {
        assertBinding({ rule, binding: emptyBinding() }, []);
      }
    }
  }
  function assertTuple(tuple, theRules = rules) {
    for (let rule of theRules) {
      for (let { spot, rest } of splitRule(rule.body, tag(tuple))) {
        // bind new tuple
        let context = evalQuery(
          { db: new DB([tuple]), js, relationTypes },
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
    dbAggregates.addTuple(tuple);
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
    return core.concat([weight]);
  }
  // actually makes worklist into a stack
  function queueTupleAdd(tuple) {
    log("queueTupleAdd: ", ppTuple(tuple));
    state.addWorklist.push(tuple);
  }
  function queueTupleDel(tuple) {
    log("queueTupleDel: ", ppTuple(tuple));
    state.delWorklist.push(tuple);
  }
  function bindingEq(b1, b2) {
    return b1.eq(b2, valEqual);
  }
  function insertAtom(db, atom, id, binding) {
    let c = core(atom);
    if (!containsAtom(db, c, id, binding))
      db.add(c, { id, binding, weight: weight(atom) });
  }
  function containsAtom(db, c, id, binding) {
    return db.get(c).some(({ id: i, binding: b }) => i === id && bindingEq(b, binding));
  }
  function removeAtom(db, atom, id, binding) {
    db.update(core(atom), (arr) =>
      arr.filter(({ id: i, binding: b }) => i !== id || !bindingEq(b, binding))
    );
  }
  function tupleEqual(t1, t2) {
    return key(t1) === key(t2);
  }
  function retractTuple(tuple) {
    log("retractTuple: ", ppTuple(tuple));
    for (let ruleBinding of dependencies.get(tuple)) {
      log("retractBinding: ", ruleBinding);
      retractBinding(ruleBinding);
    }
    dependencies.reset(tuple);
    state.addWorklist = state.addWorklist.filter((t) => !tupleEqual(t, tuple));
    dbAggregates.remove(core(tuple));
  }
  function retractBinding(x) {
    changeBinding(x, "del");
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
  assert(isVar(term) || isHole(term));
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

// External interface to add/remove tuples
function addAtom(state, c, w = mkInt(1)) {
  state.atomWorklist.push([...c, w]);
}

export {
  fixRules,
  emptyState,
  evalQuery,
  substitute,
  addAtom,
  reductionType,
  core,
  weight,
  mkSeminaive,
  fixQuery,
};
