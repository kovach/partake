import { assert, MonoidMap, splitArray, toTag } from "./collections.js";
import {
  fixRules,
  mkProgram,
  emptyState,
  seminaive,
  addTuple,
  delTuple,
} from "./derive.js";
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
import { parseNonterminal, parseProgram } from "./parse.js";

let unitTest2 = [
  "datalog2",
  () => {
    let rules = fixRules(
      parseNonterminal(
        "derivation_block",
        `
---
root 1, adj 1 2 1, adj 2 3 1, adj 3 4 1, adj 1 4 22.

root a --- dist a -> 0.
dist a -> d --- foo a -> d.
dist x -> d1, adj x y d2 --- dist y -> @add(d1, d2).
`
      )
    );
    let { state, program } = setupState(rules, js, {
      dist: "min",
      foo: "num",
    });
    seminaive(program, state);
    assert(state.dbAggregates.map.size === 12);
    return state;
  },
];
let unitTest3 = [
  "datalog3",
  () => {
    let rules = fixRules(
      parseNonterminal(
        "derivation_block",
        `
---
node 1, node 2, node 3, node 4,
adj 1 2 1, adj 2 3 1, adj 3 4 1, adj 1 4 22.

node a --- dist a a -> 0.
dist a b -> d1, adj b c d2 --- dist a c -> @add(d1, d2).
`
      )
    );
    let { state, program } = setupState(rules, js, { dist: "min" });
    seminaive(program, state);
    assert(state.dbAggregates.map.size === 18);
    return state;
  },
];
let unitTest4 = [
  "datalog4",
  () => {
    let ruleText0 = `
---
land 1, land 2, land 3, land 4,
land 5, land 6, land 7, land 8.
`;
    // omit land 1
    let ruleText1 = `
---
land 2, land 3, land 4,
land 5, land 6, land 7, land 8.
`;
    // board C
    let ruleText2 = `
---
adjacent 1 2, adjacent 1 5, adjacent 1 6,
adjacent 2 3, adjacent 2 4, adjacent 2 5,
adjacent 3 4, adjacent 4 5, adjacent 4 7,
adjacent 5 6, adjacent 5 7,
adjacent 6 7, adjacent 6 8,
adjacent 7 8.

adjacent A B --- adj A B.
adjacent A B --- adj B A.

land A
------
dist A A -> 0.

dist A B -> D, adj B C
----------------------
dist A C -> @add(D, 1).
`;
    let rules0 = fixRules(parseNonterminal("derivation_block", ruleText0 + ruleText2));
    let rules1 = fixRules(parseNonterminal("derivation_block", ruleText1 + ruleText2));
    {
      let { state, program } = setupState(rules0, js, { dist: "min" });
      timeFn(() => seminaive(program, state));
      assert(state.dbAggregates.map.size === 114);
    }
    {
      let { state, program } = setupState(rules1, js, { dist: "min" });
      seminaive(program, state);
      assert(state.dbAggregates.map.size === 105);
      addTuple(state, ["land", mkInt(1)]);
      seminaive(program, state);
      // 9 more tuples: 8 `dist` and 1 `land`
      assert(state.dbAggregates.map.size === 114);
    }
    return null;
  },
];

let js = {
  incr: ({ value: a }) => mkInt(a + 1),
  add: ({ value: a }, { value: b }) => mkInt(a + b),
};

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
function tor(name, fn) {
  return (...args) => (fn(...args) ? [[...args]] : []);
}
let _true = mkInt(1);
let tr = (x) => x.map((x) => [...x, _true]);
function someRelation(i, o) {
  return tr([[i, i]]);
}
let single =
  (fn) =>
  (...args) =>
    tr([fn(...args)]);

let branchCounters = new MonoidMap(
  () => 0,
  (a, b) => a + b
);
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

node _ id --- reach id id.
then _ X, reach X Z, contains Z Y --- reach X Y.
then X _, reach X Z, contains Z Y --- reach X Y.

then A B, reach A X, reach B Y --- before X Y.

############## Updates ##############

######### Rule Activation
# TODO:
#node tag id _, rule name tag 'before body, @initBranch name body x
#>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
#node '_branch new parent, body new -> x, then new id.
#node tag id _, finished id, rule name tag 'after body, @initBranch name body x
#>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
#node '_branch new parent, body new -> x, then id new.

node tag id, rule name tag 'during body, @initBranch name body L B
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node '_branch New, contains id New, body New -> B, label New L, steps New -> 1.

######### Branch Update
force L -> n, label I L, steps I -> m, @lt m n, body I -> B, @updateBranch I B B'
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
body I -> B', steps I -> 1.

--- force 'start_0 -> 7.
`;

function initBranch(name, body) {
  let count = branchCounters.add(name, 1);
  return [
    name,
    body,
    mkSym(name.value + "_" + count),
    mkBox({ binding: emptyBinding(), body: body.value }),
  ];
}
function mainTest(stories) {
  let relTypes = {
    delay: "max",
    "next-delay": "min",
    body: "last",
    force: "num",
    steps: "num",
  };

  function updateBranch(id, box) {
    let {
      value: { binding, body },
    } = box;
    console.log("!!!!", id, binding, body);
    let [op, rest] = splitArray(body);
    switch (op.tag) {
      case "do":
        console.log("do");
        break;
      default:
        throw "";
    }
    let result = mkBox({ ...box.value });
    result.value.body = rest;
    //console.log("??", result);
    return [id, box, result];
  }
  let derivations = parseRules(mainProgram);
  let js = {
    log: (...args) => {
      console.log("!!!!!!!!!! ", ...args);
    },
    someRelation,
    initBranch: single(initBranch),
    updateBranch: single(updateBranch),
    add: ({ value: a }, { value: b }) => mkInt(a + b),
    eq: tor("eq", (a, b) => {
      return valEqual(a, b);
    }),
    lt: tor("lt", (a, b) => {
      //console.log(a, b);
      //console.log(a.value < b.value);
      return a.value < b.value;
    }),
    length: (a) => mkInt(a.value.length),
    nonemptyBody: tor("nonemptyBody", ({ value: { body } }) => {
      console.log("HH", body);
      return body.length > 0;
    }),
  };
  let { program, state } = setupState(derivations, js, relTypes);
  let s = toTag(mkSym);
  let no = mkSym(null);
  for (let [type, ruleGroup] of Object.entries(stories)) {
    for (let [trigger, rules] of ruleGroup.map.entries()) {
      for (let { id, body } of rules) {
        console.log("rule: ", id, type, trigger, body);
        addTuple(state, ["rule", mkSym(id), mkSym(trigger), mkSym(type), mkBox(body)]);
      }
    }
  }
  let tup =
    (...args) =>
    () =>
      addTuple(state, [...args]);
  mkNode(state, s`game`);
  let log = [
    //tup("force", mkSym("start_0")),
    //tup("force", mkSym("turn_0")),
    //tup("force", mkSym("turn_1")),
  ];
  timeFn(() => seminaive(program, state));
  for (let t of log) {
    t();
    timeFn(() => seminaive(program, state));
  }
  printDb(state);
  console.log("db.size: ", state.dbAggregates.map.size);
}

function printDb(state) {
  function pp(ps) {
    return ps
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([tag, ...terms]) => [tag].concat(terms.map(ppTerm)).join(" "))
      .join("\n");
  }
  console.log(pp(af(state.dbAggregates.map.values()).map(([v, _]) => v)));
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
// delete tuple in >>>
// update function
//   new code for ~
//   choose
// temporal pattern

// query live db interface
