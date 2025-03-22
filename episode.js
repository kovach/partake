import { assert, KeyedMap } from "./collections.js";
import { addAtom, core, fixQuery, substitute, weight } from "./derive.js";
import { af, Binding, evalTermStrict, freshId, uniqueInt } from "./join.js";
import { parseNonterminal } from "./parse.js";

// todo: (pick n), random
let Actor = {
  all: "all",
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
  seq: (a, b) => {
    if (b.tag === "ep/done") return a;
    return episode.branch(
      { tag: Actor.seq },
      {
        1: a,
        2: b,
      }
    );
  },
};

let operation = {
  done: () => ({ tag: "op/done" }),
  /* ? */ observation: (pattern, k) => ({ tag: "observation", pattern, k }),
  /* + */ assert: (tuple, k) => ({ tag: "assert", tuple, k }),
  /* ~ */ do: (name, pairs, k) => ({ tag: "do", name, pairs, k }),
  /* branch */ cases: (actor, cases) => ({ tag: "cases", actor, cases }),
  /* choose */ choose: (actor, value, k) => ({ tag: "choose", actor, value, k }),
  /* ~x := y */ indexical: (id, term) => ({ tag: "indexical", id, term }),

  // todo
  /* helpers... if, not, may */

  seq: (a, b) => {
    if (b.tag === "op/done") return a;
    return operation.cases(
      { tag: Actor.seq },
      {
        1: a,
        2: b,
      }
    );
  },
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
function objSize(o) {
  return v(o).length;
}
function kv(o) {
  return af(Object.entries(o));
}
function v(o) {
  return af(Object.values(o));
}

function getActor(_tag) {
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
      assert(input === Input.none);
      return episode;
    case "tip":
      let { value } = episode;
      return stepTip(ec, parent, value, input);
    case "branch": {
      let { actor, cases } = episode;
      let def = (filter) => {
        assert(kv(cases).some(([k, _v]) => input[k]));
        assert(kv(input).every(([k, v]) => cases[k]));
        let x = {
          ...episode,
          cases: objFilterMap(cases, (child, key) =>
            input[key] !== undefined
              ? processInput(ec, parent, child, input[key])
              : filter
              ? undefined
              : { ...child }
          ),
        };
        return x;
      };
      switch (actor.tag) {
        case Actor.any:
        case Actor.seq:
          return def(false);
        case Actor.all:
          return def(false); // ignored
        case Actor.eq: {
          return {
            ...def(true),
            actor: { tag: Actor.all },
          };
        }
        default:
          debugger;
      }
    }
    default:
      debugger;
  }
}

let Input = {
  poke: "poke",
  stop: "stop",
  none: "none",
};

function canonUpdate(episode) {
  switch (episode.tag) {
    case "node":
      return canonUpdate(episode.body);
    case "ep/done":
      return Input.none;
    case "tip":
      let {
        value: { operation },
      } = episode;
      if (canonicalOperation(operation)) return Input.poke;
      return undefined;
    case "branch":
      let { actor, cases } = episode;
      switch (actor.tag) {
        case Actor.any:
          // don't return "all canonUpdate" bc user might not want to run all
          if (objSize(cases) === 1) {
            let out = objFilterMap(cases, canonUpdate);
            if (objSize(out) === objSize(cases)) return out;
          }
          return undefined;
        case Actor.seq:
          for (let [key, val] of kv(cases)) {
            if (episodeDone(val)) continue;
            let mv = canonUpdate(val);
            if (mv) return { [key]: mv };
            return undefined;
          }
        case Actor.all: {
          let out = objFilterMap(cases, canonUpdate);
          if (objSize(out) === objSize(cases)) return out;
          return undefined;
        }
        case Actor.eq:
          return undefined;
        default:
          debugger;
      }
    default:
      debugger;
  }
}

function intoUpdate(op, episode) {
  switch (episode.tag) {
    case "node":
      return intoUpdate(op, episode.body);
    case "ep/done":
      return Input.none;
    case "tip":
      return op;
    case "branch":
      let { actor, cases } = episode;
      switch (actor.tag) {
        case Actor.any:
        case Actor.eq:
          let out = objFilterMap(cases, (v, k) => {
            return op[k] ? intoUpdate(op[k], v) : undefined;
          });
          return out;
        case Actor.seq:
          for (let [key, val] of kv(cases)) {
            if (episodeDone(val)) continue;
            let mv = intoUpdate(op, val);
            if (mv) return { [key]: mv };
            throw "unreachable";
          }
        case Actor.all: {
          let out = objFilterMap(cases, (v, k) => {
            assert(op[k]);
            return intoUpdate(op[k], v);
          });
          if (objSize(out) === objSize(cases)) return out;
          throw "";
        }
        default:
          debugger;
      }
    default:
      debugger;
  }
}

function canonicalOperation(op) {
  switch (op.tag) {
    case "op/done": // needs to convert into episode.done
    case "cases": // just convert
    case "observation":
    case "assert":
    case "do":
    case "indexical":
      return true;
    case "choose":
      return false; // todo
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

  if (choice === Input.stop) {
    return done();
  }

  if (operation.tag !== "choose") assert(choice === Input.poke);

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
      let atom = substitute(defs.js, parentNode, binding, pattern, true);
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
    case "indexical": {
      let { id, term } = operation;
      let x = evalTermStrict(defs.js, parentNode, binding, term);
      setIndexical(id, x, parentNode);
      return done();
    }
    default:
      debugger;
  }

  function done() {
    return episode.done();
  }
}

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
    case "deictic":
      let { id, value } = op;
      return br(operation.indexical(id, value));
    // if, not
    default:
      debugger;
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
  processInput,
  filterDone,
  json,
  ppe,
  Input,
  canonUpdate,
  intoUpdate,
};
