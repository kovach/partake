import { assert, KeyedMap } from "./collections.js";
import { addAtom, core, fixQuery, substitute, weight } from "./derive.js";
import { af, Binding, freshId, uniqueInt } from "./join.js";
import { parseNonterminal } from "./parse.js";

function json(e) {
  switch (e.tag) {
    case "node": {
      let { tag, name, body } = e;
      return { tag, name, body: json(body) };
    }
    case "branch": {
      let { tag, actor, cases } = e;
      return { tag, actor, cases: objMap(cases, json) };
    }
    case "tip": {
      let { tag, value } = e;
      return { tag, value };
    }
    case "done": {
      let { tag } = e;
      return { tag };
    }
  }
}

function ppe(e) {
  switch (e.tag) {
    case "node": {
      let { tag, name, body } = e;
      return `[${name}: ${ppe(body)}]`;
    }
    case "branch": {
      let { tag, actor, cases } = e;
      return kv(objMap(cases, ppe))
        .map(([k, v]) => `(${k}: ${v})`)
        .join(" ");
    }
    case "tip": {
      let { tag, value } = e;
      return JSON.stringify({ tag, value });
    }
    case "done": {
      return "done";
    }
  }
}

function convertToNewOp(operations) {
  if (operations.length === 0) return operation.done();
  let [op, ...rest] = operations;
  let k = convertToNewOp(rest);
  function br(v) {
    return operation.seq(v, k);
  }
  switch (op.tag) {
    case "assert": {
      let { tuple } = op;
      return operation.assert(tuple, k);
    }
    case "do": {
      let {
        value: { name, tuples },
      } = op;
      return operation.do(name, tuples, k);
    }
    case "observation": {
      let { pattern } = op;
      return operation.observation(pattern, k);
    }
    case "choose": {
      let { quantifier, value } = op;
      return operation.choose(quantifier, value, k);
    }
    case "branch": {
      let { quantifier, value } = op;
      return br(
        operation.cases(
          quantifier,
          Object.fromEntries(value.map(({ id, body }) => [id, convertToNewOp(body)]))
        )
      );
    }
    case "subStory": {
      let { story } = op;
      return br(convertToNewOp(story));
    }
    // if, not, deictic
    default:
      debugger;
  }
}

// todo: (pick n), random
let Actor = {
  all: "all now",
  any: "any",
  seq: "<",
  eq: "eq",
};

let episode = {
  // branch according to actor
  branch: (actor, cases) => ({
    tag: "branch",
    actor,
    cases,
  }),
  // stores indexicals
  node: (name, body, vars) => ({ tag: "node", id: freshId(), name, body, vars }),
  tip: (value) => ({ tag: "tip", value }),
  done: () => ({ tag: "ep/done" }), // could use empty branch instead?
};

let operation = {
  done: () => ({ tag: "op/done" }),
  /* ? */ observation: (pattern, k) => ({ tag: "observation", pattern, k }),
  /* + */ assert: (tuple, k) => ({ tag: "assert", tuple, k }),
  /* ~ */ do: (name, pairs, k) => ({ tag: "do", name, pairs, k }),
  /* branch */ cases: (actor, cases) => ({ tag: "cases", actor, cases }),
  /* choose */ choose: (actor, value, k) => ({ tag: "choose", actor, value, k }),
  /* ~x := y */ deixis: (id, term) => ({ id, term }),

  // todo
  /* helpers... if, not, may */
};
let tip = {
  mk: (binding, operation) => ({ binding, operation }),
};

function objMap(o, f) {
  return Object.fromEntries(af(Object.entries(o)).map(([k, v]) => [k, f(v, k)]));
}
function objFilterMap(o, f) {
  return Object.fromEntries(
    af(Object.entries(o))
      .map(([k, v]) => {
        let x = f(v, k);
        return x !== undefined ? [k, x] : undefined;
      })
      .filter((x) => x !== undefined)
  );
}
function kv(o) {
  return af(Object.entries(o));
}
function v(o) {
  return af(Object.values(o));
}

function getActor(tag) {
  return { tag: Actor.seq }; // todo allow custom
}

function newVars(parent) {
  let binding = new Binding();
  return { binding, parent };
}
function setIndexical(tag, value, node) {
  node.vars.binding.set(tag, value);
}

function newEpisode(tag, during, parent = null) {
  // todo check order
  let bodies = during.get(tag).reverse();
  let cases = {};
  for (let { id, body } of bodies) {
    if (cases[id]) id = id + uniqueInt(); // TODO
    cases[id] = episode.tip(tip.mk(new Binding(), body));
  }
  let node = episode.node(tag, episode.branch(getActor(tag), cases), newVars(parent));
  setIndexical(tag, node.id, node);
  return node;
}

function processInput(ec, parent, episode, input) {
  switch (episode.tag) {
    case "node":
      return { ...episode, body: processInput(ec, episode, episode.body, input) };
    case "ep/done":
      assert(input === null);
      return episode;
    case "tip":
      let { value } = episode;
      if (canonicalOperation(value.operation)) {
        assert(input === null);
        return stepTip(ec, parent, value, null);
      }
      assert(input.length !== null);
      //let [choice] = input;
      return stepTip(ec, parent, value, input);
    case "branch": {
      let { actor, cases } = episode;
      let def = () => {
        assert(kv(cases).some(([k, _v]) => input[k] !== undefined));
        // assert all input included in cases
        let x = {
          ...episode,
          cases: objMap(cases, (child, key) =>
            input[key] ? processInput(ec, parent, child, input[key]) : { ...child }
          ),
        };
        return x;
      };
      switch (actor.tag) {
        case Actor.any:
          let x = kv(cases).filter(([_k, x]) => !episodeDone(x));
          if (x.length === 1) {
            let [[k, child]] = x;
            return {
              ...episode,
              // remove done cases
              cases: { [k]: processInput(ec, parent, child, input) },
            };
          } else {
            return def();
          }
        case Actor.seq:
          for (let [k, child] of kv(cases)) {
            if (episodeDone(child)) continue;
            return {
              ...episode,
              cases: { ...cases, [k]: processInput(ec, parent, child, input) },
            };
          }
          throw "unreachable";
        case Actor.all:
          // todo: assert coverage?
          return {
            ...episode,
            cases: objMap(cases, (v) => processInput(ec, parent, v, input)),
          };
        case Actor.eq: {
          // assume always explicit choice
          let newCases = objFilterMap(cases, (child, key) =>
            input[key] !== undefined
              ? processInput(ec, parent, child, input[key])
              : undefined
          );
          assert(v(newCases).length === actor.count);
          let x = {
            ...episode,
            actor: { tag: Actor.all },
            cases: newCases,
          };
          return x;
        }
        default:
          debugger;
      }
    }
    default:
      debugger;
  }
}
function canonicalEpisode(episode) {
  switch (episode.tag) {
    case "node":
      return canonicalEpisode(episode.body);
    case "ep/done":
      return true; // ?
    case "tip":
      let {
        value: { operation },
      } = episode;
      return canonicalOperation(operation);
    case "branch":
      let { actor, cases } = episode;
      switch (actor.tag) {
        case Actor.any:
          let cs = v(cases).filter((x) => !episodeDone(x));
          return cs.length === 1 && canonicalEpisode(cs[0]);
        case Actor.seq:
          for (let val of v(cases)) {
            if (episodeDone(val)) continue;
            return canonicalEpisode(val);
          }
          return true;
        case Actor.all:
          return children(episode).every(canonicalEpisode);
        case Actor.eq:
          return false;
        default:
          debugger;
      }
    default:
      debugger;
  }
}

function children(episode) {
  assert(episode.tag === "branch");
  return v(episode.cases);
}

episode.seq = (a, b) => {
  return episode.branch(
    { tag: Actor.seq },
    {
      1: a,
      2: b,
    }
  );
};

operation.seq = (a, b) => {
  return operation.cases(
    { tag: Actor.seq },
    {
      1: a,
      2: b,
    }
  );
};

function canonicalOperation(op) {
  switch (op.tag) {
    case "op/done": // needs to convert into episode.done
    case "cases": // just convert
    case "observation":
    case "assert":
    case "do":
    case "deixis":
      return true;
    case "choose":
      return false; // todo
      debugger;
    default:
      debugger;
  }
}
function filterDone(episode) {
  switch (episode.tag) {
    case "branch":
      let vs = v(episode.cases);
      if (vs.length === 1) {
        return filterDone(vs[0]);
      }
      return {
        ...episode,
        cases: objFilterMap(episode.cases, (v) =>
          episodeDone(v) ? undefined : filterDone(v)
        ),
      };
    case "node":
      return { ...episode, body: filterDone(episode.body) };
    case "ep/done":
    case "tip":
      return episode;
    default:
      debugger;
  }
}

function episodeDone(episode) {
  switch (episode.tag) {
    case "branch":
      return v(episode.cases).every(episodeDone);
    case "node":
      return episodeDone(episode.body);
    case "ep/done":
      return true;
    case "tip":
      return false;
    default:
      debugger;
  }
}

function tp(b, x) {
  return episode.tip(tip.mk(b, x));
}

function stepTip({ ec, rules }, parentNode, { binding, operation }, choice) {
  let state = ec.getState();
  let defs = ec.defs;
  let location = parentNode;

  switch (operation.tag) {
    case "op/done":
      return done();
    case "do":
      let { name, pairs, k } = operation;
      // todo: substitute pairs
      let it = newEpisode(name, rules.during, parentNode);
      return episode.seq(it, tp(binding, k));
    case "assert": {
      let {
        tuple: { tag, terms },
        k,
      } = operation;
      let pattern = [tag, ...terms];
      binding = binding.clone();
      let atom = substitute(defs.js, location, binding, pattern, true);
      addAtom(state, core(atom), weight(atom));
      return tp(binding, k);
    }
    case "observation": {
      let {
        k,
        pattern: { tag, terms },
      } = operation;
      let pattern = [tag].concat(terms);
      let bindings = ec.query(parentNode, [pattern], binding);
      if (bindings.length === 0) {
        return done();
      } else {
        let tips = bindings.map((b) => tp(b, k));
        return episode.branch({ tag: Actor.all }, tips);
      }
    }
    case "cases": {
      let { actor, cases } = operation;
      return episode.branch(
        actor,
        objMap(cases, (c) => episode.tip(tip.mk(binding, c)))
      );
    }
    case "choose": {
      let bindings;
      let { actor, value, k } = operation;
      // initially solve query, or filter options based on `choice`
      if (value.query) {
        let query = fixQuery(value.query);
        bindings = ec.query(parentNode, query, binding);
      } else {
        assert(value.options);
        bindings = value.options;
      }
      let initialLength = bindings.length;
      bindings = bindings.filter((b) => choice.le(b));
      //assert(bindings.length < initialLength, "irrelevant choice");
      //debugger;
      switch (actor.tag) {
        case "eq":
          assert(bindings.length >= actor.count, "invalid choice");
          if (bindings.length === actor.count) {
            return episode.branch(
              { tag: Actor.all },
              bindings.map((b) => tp(b, k))
            );
          }
          break;
        case "random":
          debugger;
          bindings = randomSample(bindings, quantifier.count);
          return bindings.map(mkRest);
      }
      return tp(binding, { ...operation, value: { options: bindings } });
    }
    default:
      debugger;
  }

  function done() {
    return episode.done();
    return { binding, operation: operation.done() };
  }
}
export {
  Actor,
  episode,
  operation,
  tip,
  episodeDone,
  convertToNewOp,
  newEpisode,
  canonicalEpisode,
  processInput,
  filterDone,
  json,
  ppe,
};
