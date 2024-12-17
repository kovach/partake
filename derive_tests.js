import { assert } from "./collections.js";
import {
  fixRules,
  mkProgram,
  emptyState,
  seminaive,
  addTuple,
  delTuple,
} from "./derive.js";
import { mkInt } from "./join.js";
import { parseNonterminal } from "./parse.js";

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

function timeFn(fn) {
  let t0 = performance.now();
  fn();
  let t1 = performance.now();
  let ms = t1 - t0;
  console.log("time: ", ms);
  return ms;
}

let js = {
  incr: ({ value: a }) => mkInt(a + 1),
  add: ({ value: a }, { value: b }) => mkInt(a + b),
};

function setupState(rules, js, relationTypes) {
  return { state: emptyState(), program: mkProgram(rules, js, relationTypes) };
}

function runTests() {
  let unitTests = new Map([unitTest2, unitTest3, unitTest4]);
  for (let [key, val] of unitTests.entries()) {
    console.log(key, val());
  }
}
export { runTests };
