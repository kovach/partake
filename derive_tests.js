import { assert, range, MonoidMap, splitArray, toTag } from "./collections.js";
import { parseNonterminal, parseProgram } from "./parse.js";
import {
  emptyBinding,
  freshId,
  mkInt,
  mkSym,
  mkBox,
  mkBind,
  valEqual,
  af,
  ppTuples,
  ppTerm,
} from "./join.js";
import {
  fixRules,
  evalQuery,
  substitute,
  addTuple,
  delTuple,
  core,
  weight,
  mkSeminaive,
  fixQuery,
  addTupleWeight,
} from "./derive.js";

function parseRules(text) {
  let removeCommentFromLine = (s) => /[^#]*/.exec(s);
  let removeComments = (text) => text.split("\n").map(removeCommentFromLine).join("\n");
  return fixRules(parseNonterminal("derivation_block", removeComments(text)));
}

function mkNode(state, tag) {
  let id = freshId();
  addTuple(state, ["node", id]);
  addTuple(state, ["id-tag", id, tag]);
  return id;
}
function mkChildNode(state, tag, parent) {
  let newId = mkNode(state, tag);
  addTuple(state, ["contains", parent, newId]);
  return newId;
}
function tor(name, fn) {
  return (...args) => (fn(...args) ? [[...args]] : []);
}
let tr = (x) => x.map((x) => [...x, _true]);
let single =
  (fn) =>
  (...args) =>
    tr([fn(...args)]);

function loadRuleTuples(state, stories) {
  for (let [type, ruleGroup] of Object.entries(stories)) {
    for (let [trigger, rules] of ruleGroup.map.entries()) {
      for (let { id, body } of rules) {
        //console.log("rule: ", id, type, trigger, body);
        addTuple(state, ["rule", mkSym(id), mkSym(trigger), mkSym(type), mkBox(body)]);
      }
    }
  }
}
const mainProgram = `
node _ id --- node id.
node '_branch id --- is-branch id.

node id --- reach id id.
reach X Z, contains Z Y --- reach X Y.
then A B, reach A X, reach B Y --- before X Y.

succeeds I I' --- old I.
node I, body I _ S, @lt 0 @length(S), old I -> 0 --- tip I.

# TODO needed?
#delay e -> a, next-delay -> b, @lt a b --- finished e.
#node id --- delay id -> 0.
#before x y, delay x -> a --- delay y -> @add(a,1).
#unfinished x, delay x -> val --- next-delay -> val.
#is-branch id, delay id -> v, next-delay -> v --- active id.
#node '_branch id, body id -> body, @nonemptyBody body
#--- unfinished id.
#node x, reach x y, unfinished y --- unfinished x.

############## Updates ##############

######### Rule Activation

id-tag I T, rule name T 'during Body, @initBranch name Body L
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node I', contains I I', body I' {} Body, label I' L.

######### Branch Update

force x L B --- force x L B {}.

!force x L BindPattern Choice, label I L, tip I, contains P I,
body I B S, @le BindPattern B, @updateBranch P I B S Choice B' S'
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node I', body I' B' S', label I' L, succeeds I I', contains P I'.

# Diagnostic
body I B S, label I L --- remaining-steps I L @length(S).
tip I, label I L, body I B S, contains P I --- z P I L B S.
`;

let branchCounters = new MonoidMap(
  () => ({
    count: 0,
  }),
  (l, r) => (l.count += r)
);
function initBranch(name, body) {
  let { count } = branchCounters.add(name.value, 1);
  return [name, body, mkSym(name.value + "_" + count)];
}

let _true = mkInt(1);
let updateBranch = (ec, parent, id, bind, story, choice) => {
  let state = ec.getState();
  let defs = ec.defs;
  let binding = bind.value;
  let body = story.value;
  let [op, rest] = splitArray(body);
  function mkRest(binding) {
    return [parent, id, bind, story, choice, mkBind(binding), mkBox(rest), _true];
  }
  function mkCurrent(binding, newStory) {
    return [parent, id, bind, story, choice, mkBind(binding), mkBox(newStory), _true];
  }
  switch (op.tag) {
    case "do":
      let { name, tuples } = op.value;
      let newChild = mkChildNode(state, mkSym(name), id);
      for (let { tag, terms } of tuples) {
        let tuple = [tag, newChild, ...core(terms)];
        tuple = substitute(defs.js, binding, tuple, true);
        addTuple(state, tuple);
      }
      return [mkRest(binding)];
    case "observation": {
      let pattern = [op.pattern.tag].concat(op.pattern.terms);
      let bindings = af(
        evalQuery(
          { location: parent, db: state.dbAggregates, ...defs },
          [pattern],
          [binding]
        )
      );
      return bindings.map(mkRest);
    }
    case "assert": {
      let pattern = [op.tuple.tag].concat(op.tuple.terms);
      binding = binding.clone();
      let tuple = substitute(defs.js, binding, pattern, true);
      addTupleWeight(state, tuple);
      return [mkRest(binding)];
    }
    case "choose": {
      let bindings;
      // initially solve query, or filter options based on `choice`
      if (op.value.query) {
        let query = fixQuery(op.value.query);
        bindings = af(
          evalQuery({ location: parent, db: state.dbAggregates, ...defs }, query, [
            binding,
          ])
        );
      } else {
        assert(op.value.options);
        bindings = op.value.options;
        bindings = bindings.filter((b) => choice.value.unify(b));
        assert(bindings.length > 0, "invalid choice");
      }
      // if one option remains, proceed
      if (bindings.length === 1) {
        return [mkRest(bindings[0])];
      } else {
        let newOp = { ...op, value: { options: bindings } };
        return [mkCurrent(binding, [newOp, ...rest])];
      }
    }
    case "branch":
      op.value.forEach(({ id: _id, body }) => {
        let id = freshId();
        addTuple(state, ["node", id]);
        addTuple(state, ["body", id, mkBind(emptyBinding()), mkBox(body)]);
        addTuple(state, ["label", id, mkSym(_id)]);
        addTuple(state, ["contains", parent, id]);
      });
      return [mkRest(binding)];
    default:
      throw "";
  }
};

function mainTest(stories) {
  let relTypes = {
    delay: "max",
    "next-delay": "min",
    steps: "num",
    forceSteps: "num",
    located: "last",
  };
  let derivations = parseRules(mainProgram);

  let js = {
    log: (...args) => {
      console.log("!!!!!!!!!! ", ...args);
    },
    initBranch: single(initBranch),
    updateBranch: (...args) => updateBranch(ec, ...args),
    add: ({ value: a }, { value: b }) => mkInt(a + b),
    eq: tor("eq", (a, b) => {
      return valEqual(a, b);
    }),
    lt: tor("lt", (a, b) => {
      return a.value < b.value;
    }),
    le: tor("le", (a, b) => {
      if (a.tag === "bind") return a.value.le(b.value);
      assert(["int", "sym"].includes(a.tag));
      return a.value <= b.value;
    }),
    length: (a) => mkInt(a.value.length),
    story: ({ value: { body } }) => {
      return mkBox(body);
    },
    nonemptyBody: tor("nonemptyBody", ({ value: { body } }) => {
      return body.length > 0;
    }),
    unify: (a, b) => {
      let out = a.value.unify(b.value);
      if (out) {
        //console.log("UNIFY: ", ppTerm(out));
        return [[a, b, mkBind(out), _true]];
      }
      return [];
    },
  };

  let s = toTag(mkSym);
  let tup =
    (...args) =>
    () =>
      addTuple(state, [...args]);
  let go = (n, x) => () => range(n).map((_i) => ec.addRules(parseRules(x)));

  /* setup */
  let ec = mkSeminaive(derivations, js, relTypes);
  //let executionContext = setupState(derivations, js, relTypes);
  ec.init();
  let state = ec.getState();
  loadRuleTuples(state, stories);
  mkNode(state, s`game`);

  /* execute log of actions */
  let thelog = [
    go(6, " >>> force _ 'setup_1 {}."), // 6
    go(5, " >>> force _ 'deal_1 {}."), // 5
    go(5, " >>> force _ 'mk-card_1 {}."), // 5
    go(5, " >>> force _ 'mk-card_2 {}."), // 5

    // test push
    go(1, " >>> force _ 'foo_1 {}."), // 1
    go(2, " >>> force _ 'push_1 {}."), // 2
    go(3, " >>> force _ 'move_1 {}."), //

    go(1, " >>> force _ 'turn1_1 {}."), // 1
    go(1, " >>> force _ 'turn_1 {}."), // 6
    go(2, " >>> force _ 'spirit-phase_1 {}."), // 2
    go(1, " >>> force _ 'choose-cards_1 {} {}."), // 5
    go(4, " >>> force _ 'choose-cards_1 {P: 'P} {Name: 'instruments}."),
    go(3, " >>> force _ 'move_2 {} {}."), // 3
  ];
  timeFn(() => ec.solve());
  let i = 0;
  for (let t of thelog) {
    console.log("iter:", i++);
    timeFn(t);
  }

  /* finish */
  let omit = [
    //"foo",
    "reach",
    "remaining-steps",
    "contains",
    "old",
    "node",
    "is-branch",
    "force",
    "succeeds",
    "body",
  ];
  timeFn(() => ec.print(omit));
  console.log("db.size: ", state.dbAggregates.size()); // 740 200ms
  console.log(state);
}
function timeFn(fn) {
  let t0 = performance.now();
  fn();
  let t1 = performance.now();
  let ms = t1 - t0;
  if (ms > 0) console.log("time: ", ms);
  return ms;
}

function loadRules(fn) {
  fetch("si3.mm")
    .then((res) => res.text())
    .then((text) => fn(parseProgram(text)));
}

function main(stories) {
  timeFn(() => mainTest(stories));
}

window.onload = () => loadRules(main);

/*
! [kinda] assertion
[x]spawn episode with local tuple, match (only immediate child for now)
[x]branch
[x]"@Type Token" feature. push

setup call to isolation, gather
query *tuples hereditarily

user datalog, game board
fully qualified force (name all paths)
draft, activate, ravage
GOAL one approximate spirit island turn

after rules (access locals of trigger)
list long script examples
temporal pattern
quantifier
modify *tuples

pain issues
  label numbering
  eval until choice
    ? parse trail format
  perf

box [eq] method?
! dot expand derive rules
revive old unit tests
? immutable bindings
? enrich patterns with relationType/js content
query live db interface
save derivation traces for regression tests
delete tuples with >>>
*/
