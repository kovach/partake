import { randomSample } from "./random.js";
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
  core,
  weight,
  mkSeminaive,
  fixQuery,
  addAtom,
} from "./derive.js";

function parseRules(text) {
  let removeCommentFromLine = (s) => /[^#]*/.exec(s);
  let removeComments = (text) => text.split("\n").map(removeCommentFromLine).join("\n");
  return fixRules(parseNonterminal("derivation_block", removeComments(text)));
}

function mkNode(state, tag) {
  let id = freshId();
  addAtom(state, ["node", id]);
  addAtom(state, ["node-tag", id, tag]);
  return id;
}
function mkChildNode(state, tag, parent) {
  let newId = mkNode(state, tag);
  addAtom(state, ["contains", parent, newId]);
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
        addAtom(state, ["rule", mkSym(id), mkSym(trigger), mkSym(type), mkBox(body)]);
      }
    }
  }
}
const mainProgram = `
node _ id --- node id.
node '_branch id --- is-branch id.

succeeds I I' --- old I.
node I, body I _ S, @lt 0 @length(S), old I -> 0 --- tip I.

# TODO needed?
#node id --- reach id id.
#reach X Z, contains Z Y --- reach X Y.
#then A B, reach A X, reach B Y --- before X Y.
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

node-tag I T, rule name T 'during Body, @initBranch name Body L
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node I', contains I I', body I' {} Body, label I' L.

######### Branch Update

force x L B --- force x L B {}.

!force x L BindPattern Choice, label I L, tip I, contains P I,
body I B S, @le BindPattern B, @updateBranch P I L B S Choice L' B' S'
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node I', body I' B' S', label I' L', succeeds I I', contains P I'.

# prune this tip
!terminate x L, label I L, tip I
>>>
succeeds I _.

# Diagnostic
tip I, label I L, body I B S, contains P I --- z P I L B S.

#body I B S, label I L --- remaining-steps I L @length(S).
`;

let branchCounters = new MonoidMap(
  () => ({
    count: 0,
  }),
  (l, r) => (l.count += r)
);
function initBranch(name, body) {
  let { count } = branchCounters.add(name.value, 1);
  return [name, body, mkSym(name.value)];
  //return [name, body, mkSym(name.value + "_" + count)];
}

let _true = mkInt(1);
let labelSep = "/";
let updateBranch = (ec, parent, id, label, bind, story, choice) => {
  let state = ec.getState();
  let defs = ec.defs;
  let binding = bind.value;
  let body = story.value;
  let [op, rest] = splitArray(body);
  function mk(newLabel, binding, newStory) {
    return [
      parent,
      id,
      label,
      bind,
      story,
      choice,
      newLabel,
      mkBind(binding),
      mkBox(newStory),
      _true,
    ];
  }
  function mkRest(binding) {
    return mk(label, binding, rest);
  }
  switch (op.tag) {
    case "do":
      let { name, tuples } = op.value;
      let newChild = mkChildNode(state, mkSym(name), id);
      for (let { tag, terms } of tuples) {
        let tuple = [tag, newChild, ...core(terms)];
        tuple = substitute(defs.js, binding, tuple, true);
        addAtom(state, tuple);
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
      addAtom(state, core(tuple), weight(tuple));
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
      }
      bindings = bindings.filter((b) => choice.value.unify(b));
      assert(bindings.length > 0, "invalid choice");
      let { quantifier } = op;
      switch (quantifier.tag) {
        case "eq":
          if (bindings.length === quantifier.count) {
            return bindings.map(mkRest);
          }
          break;
        case "random":
          bindings = randomSample(bindings, quantifier.count);
          return bindings.map(mkRest);
      }
      // if one option remains, proceed
      // if (bindings.length === 1) {
      //   return [mkRest(bindings[0])];
      // } else
      {
        let newOp = { ...op, value: { options: bindings } };
        return [mk(label, binding, [newOp, ...rest])];
      }
    }
    case "branch":
      // one successor per option + 1 for the rest of the rule
      return [
        ...op.value.map(({ id: _id, body }) => {
          return mk(mkSym(label.value + labelSep + _id), binding, body);
        }),
        mkRest(binding),
      ];
    // todo: desugar this to `branch`
    case "subStory":
      return [
        mk({ ...label, value: label.value + labelSep + "1" }, binding, op.story),
        mkRest(binding),
      ];
      throw "";
    default:
      throw "";
  }
};

function mainTest(stories, userRules) {
  let relTypes = {
    located: "last",
    owner: "last",

    delay: "max",
    "next-delay": "min",

    steps: "num",
    forceSteps: "num",
    range: "min",
    energy: "num",
    "card-plays": "num",
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
      addAtom(state, [...args]);
  let go = (n, x) => () => range(n).map((_i) => ec.addRules(parseRules(x)));

  /* setup */
  let ec = mkSeminaive([...derivations, ...userRules], js, relTypes);
  ec.init();
  let state = ec.getState();
  loadRuleTuples(state, stories);
  mkNode(state, s`game`);

  /* Execute log of actions */
  // prettier-ignore
  let thelog = [
    go(8, " >>> force _ 'setup {}."), // 8
      go(4, " >>> force _ 'place-presence {} {L: 1}."), //
    go(5, " >>> force _ 'deal {}."), // 5
      go(5, " >>> force _ 'mk-card {}."), // 5

    // test misc.
    go(2, " >>> force _ 'foo {}."), // 2
      go(2, " >>> force _ 'push {} {L:2}."), // 2
      go(3, " >>> force _ 'move {}."), // 3
      go(1, " >>> force _ 'foo/a {}."), // 1
      go(1, " >>> force _ 'foo/b {}."), // 1
    go(3, " >>> force _ 'foo {}."), // 2

    go(1, " >>> force _ 'turn1 {}."),
    go(1, " >>> force _ 'turn {}."), // 6
    go(2, " >>> force _ 'spirit-phase {}."), // 2
      go(2, " >>> force _ 'spirit-grow {}."), // 2
        go(2, " >>> force _ 'deal-cards {} {}."), // 2
          go(3, " >>> force _ 'deal-cards/1 {} {}."), // 3
            go(3, " >>> force _ 'move {} {}."), // 3
        go(1, " >>> force _ 'deal-cards {} {}."), // 1
        go(5, " >>> force _ 'choose-card {} {Name: 'call}."), //
          go(3, " >>> force _ 'move {} {}."), // 3
    go(1, " >>> force _ 'spirit-phase {}."), // 2
      go(9, " >>> force _ 'play-cards {}."), // 9
        go(3, " >>> force _ 'move {} {}."), // 3
      go(1, " >>> force _ 'play-cards {}."), // 1
      go(1, " >>> terminate _ 'play-cards."), // 1
    go(1, " >>> force _ 'turn {}."),
    go(4, " >>> force _ 'power-phase {}."), // 4
      go(5, " >>> force _ 'target-call {} {Land: 1}."), // 5
        go(3, " >>> force _ 'activate-call {} {}."), //
        go(1, " >>> terminate _ 'activate-call/push-invaders."), //
        go(2, " >>> force _ 'activate-call/push-dahan {} {}."), //
          go(2, " >>> force _ 'push {} {L:4}."), //
            go(3, " >>> force _ 'move {}."), // 3
  ];
  timeFn(() => ec.solve());
  let i = 0;
  for (let t of thelog) {
    console.log("iter:", ++i);
    if (timeFn(t) === "done") break; // early exit
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
    "node-tag",
    "label",

    "land",
    "adjacent",
    "adjacent-land",
    "range",

    "rule",
  ];
  timeFn(() => ec.print(omit));
  console.log("db.size: ", state.dbAggregates.size()); // 1186 450
  console.log(state);
}
function timeFn(fn) {
  let t0 = performance.now();
  let x = fn();
  let t1 = performance.now();
  let ms = t1 - t0;
  if (ms > 0) console.log("time: ", ms);
  return x;
}

function loadRules(fn) {
  Promise.all([fetch("si3.mm"), fetch("si3.sad")])
    .then((res) => Promise.all(res.map((p) => p.text())))
    .then(([t1, t2]) => fn(parseProgram(t1), parseRules(t2)));
}

function main(stories, rules) {
  timeFn(() => mainTest(stories, rules));
}

window.onload = () => loadRules(main);

/*
! [kinda] assertion
[x]spawn episode with local tuple, match (only immediate child for now)
[x]branch
[x]"@Type Token" feature. push
[x]user datalog, SI board
[x] subStory case
[x] draft: randomize quantifier, test
[x] play-cards: pay for cards
[x] activate power, activate: choose target, activate

query *tuples hereditarily
ravage
grow: presence
GOAL one approximate spirit island turn
setup call to isolation, gather

after rules (access locals of trigger)
list long script examples
temporal pattern
quantifier
modify *tuples

pain issues
  query *tuples hereditarily
  eval until choice
  label numbering
  qualified force? parse trail format
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
