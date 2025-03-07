import { assert, toTag } from "./collections.js";
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

function mkNode(state, tag, parent, value) {
  let id = freshId();
  addTuple(state, ["node", tag, id, parent, value]);
  return id;
}
function mkBranch(state, rule, parent) {
  return mkNode("branch", parent, mkObj({ binding: emptyBinding(), rule }));
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

function initBranch(body) {
  return [body, mkBox({ binding: emptyBinding(), body })];
}
function updateBranch({ value: { binding, body } }) {
  console.log("!!!!", binding, body);
}
const mainProgram = `
delay e -> a, next-delay -> b, @lt a b --- finished e.

node _ id _ _ --- node id.
node '_branch id _ _ --- is-branch id.

node '_branch id _ body, @lt 0 @length(body)
--------------------------------------------
unfinished id.

node parent, reach parent x, unfinished x --- unfinished parent.

node id --- delay id -> 0.
before x y, delay x -> a --- delay y -> @add(a,1).
unfinished x, delay x -> val --- next-delay -> val.

is-branch id, delay id -> v, next-delay -> v --- active id.

node _ id parent _
--- pc parent id.

node _ id _ _ --- reach id id.

then _ X, reach X Z, pc Z Y --- reach X Y.

then A B, reach A X, reach B Y --- before X Y.

############## Updates ##############

######### Rule Activation
node tag id parent _, rule tag 'before body, @init-branch body x
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node '_branch new parent x, then new id.

node tag id parent _, rule tag 'during body
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node '_branch new id body.

node tag id parent _, finished id, rule tag 'after body
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node '_branch new parent x, then id new.

######### Branch Update
force id, node '_branch id _ body
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
@update-branch(body).
`;

function mainTest(stories) {
  let derivations = parseRules(mainProgram);
  let relTypes = { delay: "max", "next-delay": "min" };
  let js = {
    log: (...args) => {
      console.log("!!!!!!!!!! ", ...args);
    },
    someRelation,
    "init-branch": single(initBranch),
    "update-branch": updateBranch,
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
    force: (x) => {
      console.log("here: ", x);
      throw "todo";
    },
  };
  let { program, state } = setupState(derivations, js, relTypes);
  let s = toTag(mkSym);
  let no = mkSym(null);
  //addTuple(state, ["rule", s`turn`, s`during`, mkBox([1, 2, 3])]);
  //addTuple(state, ["rule", s`game`, s`after`, mkBox([])]);
  //addTuple(state, ["rule", s`turn`, s`before`, mkBox([])]);
  for (let [type, rules] of Object.entries(stories)) {
    for (let [trigger, rule] of rules.map.entries()) {
      console.log(type, trigger, rule);
      addTuple(state, ["rule", mkSym(trigger), mkSym(type), mkBox(rule)]);
    }
  }
  let tup = (...args) => addTuple(state, [...args]);
  let game = mkNode(state, s`game`, freshId(), no);
  //let t1 = mkNode(state, s`turn`, game, no);
  //let t2 = mkNode(state, s`turn`, game, no);
  //addTuple(state, ["then", t1, t2]);
  tup("force", game);

  timeFn(() => seminaive(program, state));
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
// temporal pattern
// log of *stable branch references*
// update function
//   new code for ~
//   choose

// query live db interface
