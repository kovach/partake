import { assert, enumerate, KeyedMap } from "./collections.js";
import { addAtom, core, substitute, weight } from "./derive.js";
import { af, Binding, freshId, uniqueInt } from "./join.js";
let Actor = {
  all: "all now",
  any: "pick",
  seq: "<",
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
  /* + */ assert: (tuple) => ({ tag: "assert", tuple }),
  /* branch */ cases: (actor, cases) => ({ tag: "cases", actor, cases }),
  /* ~ */ do: (name, pairs) => ({ tag: "do", name, pairs }),
  /* choose */ choose: (actor, value, k) => ({ actor, value, k }),
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
        return x ? [k, x] : null;
      })
      .filter((x) => x)
  );
}
function kv(o) {
  return af(Object.entries(o));
}
function v(o) {
  return af(Object.values(o));
}

function getActor(tag) {
  return Actor.any; // todo allow custom
}

class IndexicalState {
  map = new KeyedMap((x) => JSON.stringify(x));
  node(tag, child, parent = null) {
    let binding = new Binding();
    binding.set(tag, child);
    this.map.set(child, { binding, parent });
  }
  set(tag, value, node) {
    this.map.get(node).binding.set(tag, value);
  }
  get(tag, node) {
    let chase = ({ binding, parent }) => {
      console.log("chas: ", tag, binding, parent);
      if (binding.has(tag)) return binding.get(tag);
      if (parent) return chase(this.map.get(parent));
    };
    console.log("..", node);
    return chase(this.map.get(node));
  }
}

function newVars(tag, parent) {
  let binding = new Binding();
  return { binding, parent };
}
function setIndexical(tag, value, node) {
  node.vars.binding.set(tag, value);
}

function newEpisode(tag, during, parent = null) {
  // todo check order
  let bodies = during.get(tag);
  let cases = {};
  for (let { id, body } of bodies) {
    if (cases[id]) id = id + uniqueInt(); // TODO
    cases[id] = episode.tip(tip.mk(new Binding(), body));
  }
  let node = episode.node(
    tag,
    episode.branch(getActor(tag), cases),
    newVars(tag, parent)
  );
  setIndexical(tag, node.id, node);
  return node;
}

// other methods on episodes
// here
function processInput(ec, parent, episode, input) {
  switch (episode.tag) {
    case "node":
      return { ...episode, body: processInput(ec, episode, episode.body, input) };
    case "ep/done":
      return episode;
    case "tip":
      let { value } = episode;
      if (canonicalOperation(value.operation)) {
        ////todo
        //assert(input.length === 0);
        //debugger;
        return stepTip(ec, parent, value, null);
      }
      //assert(input.length === 1);
      let [choice] = input;
      debugger;
      return stepTip(ec, parent, value, choice);
    case "branch": {
      let { actor, cases } = episode;
      let def = () => ({
        ...episode,
        cases: objMap(cases, (child, key) =>
          input[key] ? processInput(ec, parent, child, input[key]) : { ...child }
        ),
      });
      switch (actor) {
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
      switch (actor) {
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
//for (let [k, v] of Object.entries(episode)) {
//  episode[k] = (...args) => {
//    let episode = v(...args);
//    //episode.children = function () {
//    //  return children(this);
//    //};
//    //episode.canonical = function () {
//    //  return canonicalEpisode(this);
//    //};
//    //episode.process = function (ec, parent, input) {
//    //  return processInput(ec, parent, this, input);
//    //};
//    return episode;
//  };
//}

function convertToNewOp(operations) {
  if (operations.length === 0) return operation.done();
  let [op, ...rest] = operations;
  let k = convertToNewOp(rest);
  function br(v) {
    return operation.cases(Actor.seq, {
      1: v,
      2: k,
    });
  }
  switch (op.tag) {
    case "assert": {
      let { tuple } = op;
      return br(operation.assert(tuple));
    }
    case "do": {
      let {
        value: { name, tuples },
      } = op;
      return br(operation.do(name, tuples));
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
      return operation.cases(
        quantifier,
        value.map(({ id, body }) => [id, body])
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
function canonicalOperation(operation) {
  switch (operation.tag) {
    case "op/done": // needs to convert into episode.done
    case "cases": // just convert
    case "observation":
    case "assert":
    case "do":
    case "deixis":
      return true;
    case "choose":
      debugger;
    default:
      debugger;
  }
}
function filterDone(episode) {
  switch (episode.tag) {
    case "branch":
      return {
        ...episode,
        cases: objFilterMap(episode.cases, (v) =>
          episodeDone(v) ? null : filterDone(v)
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

/* removed args
id: folded into episode
label: not needed because labels are now local
*/
/*
parent = id of enclosing node
*/
function stepTip({ ec, rules }, parentNode, { binding, operation }, choice) {
  let state = ec.getState();
  let defs = ec.defs;
  let location = parentNode;

  switch (operation.tag) {
    case "op/done":
      return done();
    case "assert": {
      let {
        tuple: { tag, terms },
      } = operation;
      let pattern = [tag, ...terms];
      binding = binding.clone();
      let atom = substitute(defs.js, location, binding, pattern, true);
      addAtom(state, core(atom), weight(atom));
      return done();
    }
    case "do":
      let { name, pairs } = operation;
      return newEpisode(name, rules.during, parentNode);
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
        let tips = bindings.map((binding) => episode.tip(tip.mk(binding, k)));
        // here todo
        return episode.branch(Actor.all, tips);
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
      throw "";
      let bindings;
      let { value, k } = operation;
      // initially solve query, or filter options based on `choice`
      if (value.query) {
        let query = fixQuery(value.query);
        bindings = ec.query(parentNode, query, binding);
      } else {
        assert(value.options);
        bindings = value.options;
      }
      bindings = bindings.filter((b) => choice.value.unify(b));
      let { quantifier } = op;
      switch (quantifier.tag) {
        case "eq":
          assert(bindings.length >= quantifier.count, "invalid choice");
          if (bindings.length === quantifier.count) {
            return bindings.map(mkRest);
          }
          break;
        case "random":
          bindings = randomSample(bindings, quantifier.count);
          return bindings.map(mkRest);
      }
      let newOp = { ...op, value: { options: bindings } };
      return [mk(label, binding, [newOp, ...rest])];
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
};
