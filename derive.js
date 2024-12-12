import { emptyBinding, dbContains, dbAddTuple } from "./join.js";
import { KeyedMap, MonoidMap } from "./collections.js";

function seminaiveBase(rules, { db, js }) {
  let b = emptyBinding();
  for (let { head, body } of rules) {
    if (body.length === 0) {
      for (let { tag, terms } of head) {
        dbAddTuple(db, tag, substitute(js, b, terms));
      }
    }
  }
}

// todo very unoptimized
// todonow: handle nonlinearity correctly
function seminaive_(rules, { db, js }, newTuples) {
  function removeAt(array, i) {
    return array.filter((_, j) => j !== i);
  }
  function* splitRule(body, tag) {
    for (let i = 0; i < body.length; i++) {
      if (body[i].tag === tag) yield { spot: body[i], rest: removeAt(body, i) };
    }
  }
  while (newTuples.length > 0) {
    let { tag, tuple } = newTuples.pop();
    for (let { head, body } of rules) {
      for (let { spot, rest } of splitRule(body, tag)) {
        let context = [extendBinding(emptyBinding(), tag, tuple, spot.terms, [])];
        for (let binding of evalQuery(db, js, rest, context)) {
          // todo: handle weighted tuples
          for (let { tag, terms } of head) {
            let result = { tag, tuple: substitute(js, binding, terms) };
            if (!dbContains(db, result.tag, result.tuple)) {
              newTuples.push(result);
            }
          }
        }
      }
    }
    dbAddTuple(db, tag, tuple);
  }
  return null;
}

function tup(tag, values, weight) {
  return [tag].concat(values.concat([weight]));
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

  function* joinBindings(context, { tag, terms, modifiers }) {
    for (let c of context) {
      let values = terms.map((t) => evalTerm(js, c, t));
      for (let tuple of readDb(c, values)) {
        if (tupleValid(c, tag, tuple, values)) {
          yield extendBinding(c, tuple, values, modifiers || []);
        }
      }
    }
  }

  function tupleValid(c, tag, tuple, values) {
    assert(Array.isArray(values));
    if (tuple[0] !== tag) return false;
    for (let index = 0; index < values.length; index++) {
      let term = values[index];
      if (isLiteral(term) && !valEqual(term, tval(i))) return false;
    }
    return true;
  }

  function extendBinding(c, tuple, values, modifiers) {
    function tval(i) {
      return tuple[i + 1];
    }

    c = c.clone();
    for (let index = 0; index < values.length; index++) {
      let term = values[index];
      if (isVar(term)) c.set(term.value, tval(i));
    }
    modifiers.forEach((mod) => {
      c.notes.add(mod, tuple);
    });
    c.notes.add("used", tuple);
    return c;
  }
}

function singletonDb(tuple) {
  return new KeyedMap(key, [[tuple, true]]);
}

function mkState(rules, js) {
  return {
    dbAtoms: new MonoidMap(new KeyedMap(key)),
    dbAggregates: new KeyedMap(key),
    rules,
    js,
  };
}

function tag(tuple) {
  return tuple[0];
}
// drops the weight componentn
function core(tuple) {
  return tuple.slice(0, tuple.length - 1);
}

function weight(tuple) {
  return tuple[tuple.length - 1];
}

function seminaive(state, worklist) {
  let { rules, dbAtoms, dbAggregates, js } = state;
  function removeAt(array, i) {
    return array.filter((_, j) => j !== i);
  }
  /*
   * logical state: db mapping (tuple -> {(binding, weight)}), db mapping (tuple -> weight)
   * evalQuery accesses latter
   */
  function reduceFn(tag) {
    // todo
    switch (fns[tag]) {
      case "bool":
        return (a, b) => a || b;
      case "min":
        return (a, b) => Math.min(a, b);
      default:
        throw "";
    }
  }
  function getWeight(tuple) {
    let values = dbAtoms.get(core(tuple));
    return values.reduce((acc, { weight }) => reduceFn(tag(tuple))(acc, weight));
  }
  function assertTuple({ tag, tuple }) {
    for (let rule of rules) {
      for (let { spot, rest } of splitRule(rule.body, tag)) {
        let context = evalQuery(
          { db: singletonDb(tuple), js },
          [spot.terms],
          emptyBinding()
        );
        //let context = [extendBinding(emptyBinding(), tag, tuple, spot.terms, [])];
        for (let binding of evalQuery(db, js, rest, context)) {
          assertBinding({ rule, binding });
        }
      }
    }
    // TODO insert tuple
  }
  function changeBinding({ rule, binding }, mod) {
    for (let terms of rule.head) {
      // tuple -> {(binding, weight)}
      changeAtom(substitute(js, binding, terms), rule.id, binding, mod);
    }
  }
  function assertBinding(x) {
    changeBinding(x, "add");
  }
  function changeAtom(tuple, id, binding, mod) {
    let oldWeight = getWeight(tuple);
    switch (mod) {
      case "add":
        dbAtoms.add(core(tuple), { id, binding, weight: weight(tuple) });
        break;
      case "del":
        dbAtoms.update(core(tuple), (arr) =>
          arr.filter(({ id: i, binding: b }) => i !== id || !b.eq(binding))
        );
        break;
      default:
        throw "";
    }
    let newWeight = getWeight(tuple);
    if (oldWeight != newWeight) retractTuple(core(tuple));
  }
  function retractTuple(tuple) {
    for (let ruleBinding of depends(tuple)) {
      retractBinding(ruleBinding);
    }
  }
  function retractBinding(x) {
    changeBinding(x, "del");
  }
  function depends(tuple) {
    // here
  }
  function* splitRule(body, tag) {
    for (let i = 0; i < body.length; i++) {
      if (body[i].tag === tag) yield { spot: body[i], rest: removeAt(body, i) };
    }
  }
  while (newTuples.length > 0) {
    let { tag, tuple } = newTuples.pop();
    for (let { head, body } of rules) {
      for (let { spot, rest } of splitRule(body, tag)) {
        let context = [extendBinding(emptyBinding(), tag, tuple, spot.terms, [])];
        for (let binding of evalQuery(db, js, rest, context)) {
          // todo: handle weighted tuples
          for (let { tag, terms } of head) {
            let result = { tag, tuple: substitute(js, binding, terms) };
            if (!dbContains(db, result.tag, result.tuple)) {
              newTuples.push(result);
            }
          }
        }
      }
    }
    dbAddTuple(db, tag, tuple);
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

function assertTuple(t) {
  seminaive(rules, dbjs, [t]);
}

export { seminaiveBase, seminaive };
