import { assert, range, MonoidMap, splitArray, toTag } from "./collections.js";
import { parseNonterminal, parseProgram } from "./parse.js";
import {
  emptyBinding,
  freshId,
  mkInt,
  mkSym,
  mkBox,
  valEqual,
  af,
  ppTuples,
  ppTerm,
} from "./join.js";
import {
  fixRules,
  mkProgram,
  emptyState,
  evalQuery,
  substitute,
  seminaive,
  addTuple,
  delTuple,
  core,
  weight,
  reductionType,
} from "./derive.js";

function parseRules(text) {
  let removeCommentFromLine = (s) => /[^#]*/.exec(s);
  let removeComments = (text) => text.split("\n").map(removeCommentFromLine).join("\n");
  return fixRules(parseNonterminal("derivation_block", removeComments(text)));
}

function mkNode(state, tag) {
  let id = freshId();
  addTuple(state, ["node", tag, id]);
  return id;
}
function mkChildNode(state, tag, parent) {
  let newId = mkNode(state, tag);
  addTuple(state, ["contains", parent, newId]);
}
function tor(name, fn) {
  return (...args) => (fn(...args) ? [[...args]] : []);
}
let tr = (x) => x.map((x) => [...x, _true]);
let single =
  (fn) =>
  (...args) =>
    tr([fn(...args)]);

const mainProgram = `
delay e -> a, next-delay -> b, @lt a b --- finished e.

node _ id --- node id.
node '_branch id --- is-branch id.

node '_branch id, body id -> body, @nonemptyBody body
--------------------------------------------
unfinished id.

node x, reach x y, unfinished y --- unfinished x.

node id --- delay id -> 0.
before x y, delay x -> a --- delay y -> @add(a,1).
unfinished x, delay x -> val --- next-delay -> val.

is-branch id, delay id -> v, next-delay -> v --- active id.

node id --- reach id id.
then _ X, reach X Z, contains Z Y --- reach X Y.
then X _, reach X Z, contains Z Y --- reach X Y.

then A B, reach A X, reach B Y --- before X Y.

############## Updates ##############

######### Rule Activation
# TODO:
#delete: forceSteps L -> n, label I L, steps I -> m, @le m n, body I -> B, @updateBranch I B B'
#>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
#body I -> B', steps I -> 1.

#node tag id _, rule name tag 'before body, @initBranch name body x
#>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
#node '_branch new parent, body new -> x, then new id.
#node tag id _, finished id, rule name tag 'after body, @initBranch name body x
#>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
#node '_branch new parent, body new -> x, then id new.

node tag id, rule name tag 'during body, @initBranch name body L B
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node '_branch New, contains id New, body New B, label New L.

######### Branch Update
force L x, label I L, contains P I, body I B, @updateBranch I B B'
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
body I' B', label I' L', succ I I', contains P I'.

body I B, label I L --- remaining-steps I L @length(@story(B)).

succ I I' --- old I.
node I, old I -> 0 --- tip I.

`;

let branchCounters = new MonoidMap(
  () => ({
    count: 0,
  }),
  (l, r) => (l.count += r)
);
function initBranch(name, body) {
  let { count } = branchCounters.add(name.value, 1);
  return [
    name,
    body,
    mkSym(name.value + "_" + count),
    mkBox({ binding: emptyBinding(), body: body.value }),
  ];
}
function loadRuleTuples(state, stories) {
  for (let [type, ruleGroup] of Object.entries(stories)) {
    for (let [trigger, rules] of ruleGroup.map.entries()) {
      for (let { id, body } of rules) {
        console.log("rule: ", id, type, trigger, body);
        addTuple(state, ["rule", mkSym(id), mkSym(trigger), mkSym(type), mkBox(body)]);
      }
    }
  }
}

let _true = mkInt(1);
let updateBranch = (executionContext, id, box) => {
  let {
    state,
    program: { js },
  } = executionContext;
  let {
    value: { binding, body },
  } = box;
  console.log("!!!!", id, binding, body);
  let [op, rest] = splitArray(body);
  let result = mkBox({ ...box.value });
  result.value.body = rest;
  function mk(binding) {
    return [id, box, mkBox({ binding, body: rest }), _true];
  }
  switch (op.tag) {
    case "do":
      mkChildNode(state, mkSym(op.value.name), id);
      return [mk(binding)];
    case "observation": {
      let pattern = [op.pattern.tag].concat(op.pattern.terms);
      let bindings = af(evalQuery({ db: state.dbAggregates, js }, [pattern], [binding]));
      return bindings.map(mk);
    }
    // here
    case "assert": {
      let pattern = core([op.tuple.tag].concat(op.tuple.terms));
      binding = binding.clone();
      let tuple = substitute(js, binding, pattern, true);
      addTuple(state, tuple);
      return [mk(binding)];
    }
    default:
      throw "";
  }
};

function mainTest(stories) {
  let relTypes = {
    delay: "max",
    "next-delay": "min",
    //body: "last",
    steps: "num",
    forceSteps: "num",
  };
  function updateBranch_(...args) {
    return updateBranch(executionContext, ...args);
  }

  let derivations = parseRules(mainProgram);

  let js = {
    log: (...args) => {
      console.log("!!!!!!!!!! ", ...args);
    },
    initBranch: single(initBranch),
    updateBranch: updateBranch_,
    add: ({ value: a }, { value: b }) => mkInt(a + b),
    eq: tor("eq", (a, b) => {
      return valEqual(a, b);
    }),
    lt: tor("lt", (a, b) => {
      return a.value < b.value;
    }),
    le: tor("le", (a, b) => {
      return a.value <= b.value;
    }),
    length: (a) => mkInt(a.value.length),
    story: ({ value: { body } }) => {
      return mkBox(body);
    },
    nonemptyBody: tor("nonemptyBody", ({ value: { body } }) => {
      return body.length > 0;
    }),
  };

  let s = toTag(mkSym);
  let tup =
    (...args) =>
    () =>
      addTuple(state, [...args]);
  let force = (x) => tup("force", mkSym(x), freshId());
  let forcen = (n, x) => range(n).map((i) => tup("force", mkSym(x), freshId()));

  /* setup */
  let executionContext = setupState(derivations, js, relTypes);
  let { state } = executionContext;
  loadRuleTuples(state, stories);
  mkNode(state, s`game`);

  /* execute log of actions */
  // prettier-ignore
  let thelog = [
    ...forcen(1, "start_1"), // done: 1
    ...forcen(1, "setup_1"), // done: 2
    ...forcen(0, "turn_1"),  // done: 6
    ...forcen(0, 'spirit-phase_1'), // 5
  ];
  for (let t of thelog) {
    t();
    timeFn(() => seminaive(executionContext));
  }
  printExecContext(executionContext);
  console.log("db.size: ", state.dbAggregates.map.size); // 61
  console.log(state);
}

function printExecContext(executionContext) {
  let {
    program: { relationTypes },
    state: { dbAggregates },
  } = executionContext;
  function pp(ps) {
    return ps
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([tag, ...terms]) => {
        let ty = reductionType(relationTypes, tag);
        if (ty === "bool") {
          if (valEqual(weight(terms), _true)) {
            return [tag].concat(core(terms).map(ppTerm)).join(" ");
          } else {
            return [tag, ...core(terms).map(ppTerm), "->", "false"].join(" ");
          }
        } else {
          return [tag, ...core(terms).map(ppTerm), "->", ppTerm(weight(terms))].join(" ");
        }
      })
      .join("\n");
  }
  console.log(pp(af(dbAggregates.entries()).map(([core, w]) => [...core, w])));
}

function printDb(state) {
  function pp(ps) {
    return ps
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([tag, ...terms]) => {
        if (tag === "asdf") {
          console.log(">>>>>>>>>>>", terms);
        }
        return [tag].concat(terms.map(ppTerm)).join(" ");
      })
      .join("\n");
  }
  console.log(pp(af(state.dbAggregates.entries()).map(([core, w]) => [...core, w])));
}

function timeFn(fn) {
  let t0 = performance.now();
  fn();
  let t1 = performance.now();
  let ms = t1 - t0;
  console.log("time: ", ms);
  return ms;
}

function setupState(derivations, js, relationTypes) {
  return { state: emptyState(), program: mkProgram(derivations, js, relationTypes) };
}

function runTests() {
  let unitTests = new Map([unitTest2, unitTest3, unitTest4]);
  for (let [key, val] of unitTests.entries()) {
    console.log(key, val());
  }
}
export { runTests };

function loadRules(fn) {
  fetch("si3.mm")
    .then((res) => res.text())
    .then((text) => fn(parseProgram(text)));
}

function main(stories) {
  //runTests();
  mainTest(stories);
}

window.onload = () => loadRules(main);

// [x]rule invocation code
// [x]add rule to advance branch
// [x]parse and load ruleset
// [x]load rules as tuples
// [x]store correct state in branch node
// [x]stable branch reference type
// [x]iterate log of refs
// [x]duplicate tuple bug
// [kinda]assertion
// [x]split bindings,
// [x]negation, define tips
// name node by binding
// box [eq] method?
// choose
// GOAL
// update function
// delete tuple in >>>
// ! matching zero defect
// ! immutable bindings
// temporal pattern

// query live db interface
// save derivation traces for regression tests
