import { randomSample } from "./random.js";
import {
  assert,
  range,
  MonoidMap,
  splitArray,
  toTag,
  KeyedMap,
  enumerate,
} from "./collections.js";
import { parseNonterminal, parseProgram } from "./parse.js";
import {
  freshId,
  mkInt,
  mkSym,
  mkBox,
  mkBind,
  valEqual,
  af,
  ppTuples,
  ppTerm,
  Binding,
  evalTermStrict,
  isVar,
} from "./join.js";
import {
  parseRules,
  substitute,
  core,
  weight,
  mkSeminaive,
  fixQuery,
  addAtom,
} from "./derive.js";
import {
  Actor,
  canonicalEpisode,
  episode,
  episodeDone,
  filterDone,
  newEpisode,
  operation,
  processInput,
  tip,
} from "./episode.js";

Map.prototype.toJSON = function () {
  return Object.fromEntries(this);
};

function timeFn(fn) {
  let t0 = performance.now();
  let x = fn();
  let t1 = performance.now();
  let ms = t1 - t0;
  if (ms > 0) console.log("time: ", ms);
  return x;
}

// todo move
function valUnify(a, b) {
  assert(!isVar(a) || !isVar(b));
  if (!isVar(a) && !isVar(b)) return valEqual(a, b) ? [[a, b, _true]] : [];
  if (isVar(b)) return valUnify(b, a);
  return [[b, b, _true]];
}

function loadSeveral(files, fn) {
  Promise.all(files.map((f) => fetch(f)))
    .then((res) => Promise.all(res.map((p) => p.text())))
    .then((xs) => fn(xs));
}

function loadRules(fn) {
  Promise.all([fetch("si3.mm"), fetch("si3.sad")])
    .then((res) => Promise.all(res.map((p) => p.text())))
    .then(([t1, t2]) => fn(parseProgram(t1), parseRules(t2)));
}

function main(stories, rules) {
  timeFn(() => mainTest(stories, rules));
}

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
let branchCounters = new MonoidMap(
  () => ({
    count: 0,
  }),
  (l, r) => (l.count += r)
);
function initBranch(name, body) {
  // let { count } = branchCounters.add(name.value, 1);
  return [name, body, mkSym(name.value)];
}

function mkNode(state, tag) {
  let id = freshId();
  addAtom(state, ["node", id]);
  addAtom(state, ["node-tag", id, tag]);
  return id;
}
function mkRootNode(state) {
  let tag = "game";
  let id = mkNode(state, mkSym(tag));
  is.node(tag, id);
}
function mkChildNode(state, tag, parent) {
  let newId = mkNode(state, tag);
  addAtom(state, ["contains", parent, newId]);
  is.node(tag, newId, parent);
  return newId;
}

let _true = mkInt(1);
let labelSep = "/";

function updateBranchStuck(ec, parent, id, label, bind, story, choice) {
  let r = updateBranch(ec, parent, id, label, bind, story, choice);
  r.reverse();
  if (r.length === 0) return [mk(mkSym("stuck"), bind.value, [])];
  return r;

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
}

function updateBranch(ec, parent, id, label, bind, story, choice) {
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
  let location = parent;
  switch (op.tag) {
    case "do":
      let { name, tuples } = op.value;
      let newChild = mkChildNode(state, mkSym(name), parent); // todo id
      for (let { tag, terms } of tuples) {
        let tuple = [tag, newChild, ...core(terms)];
        tuple = substitute(defs.js, location, binding, tuple, true);
        addAtom(state, tuple);
      }
      return [mkRest(binding)];
    case "observation": {
      let {
        pattern: { tag, terms },
      } = op;
      let pattern = [tag].concat(terms);
      let bindings = ec.query(parent, [pattern], binding);
      if (bindings.length === 0) {
        //return [];
        return [mk(mkSym("stuck"), binding, [])];
      } else return bindings.map(mkRest);
    }
    case "assert": {
      let { when, tuple } = op;
      let pattern = [tuple.tag].concat(tuple.terms);
      binding = binding.clone();
      let atom = substitute(defs.js, location, binding, pattern, true);
      if (when !== undefined) {
        throw "";
      } else {
        addAtom(state, core(atom), weight(atom));
      }
      return [mkRest(binding)];
    }
    case "choose": {
      let bindings;
      // initially solve query, or filter options based on `choice`
      if (op.value.query) {
        let query = fixQuery(op.value.query);
        bindings = ec.query(parent, query, binding);
      } else {
        assert(op.value.options);
        bindings = op.value.options;
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
    case "countIf":
    case "countNot":
      let query = fixQuery(op.value);
      let n = ec.query(parent, query, binding).length;
      let ok = op.tag === "countIf" ? n > 0 : n === 0;
      return ok ? [mkRest(binding)] : [];
      throw "";
    case "deictic":
      let { id, value } = op;
      let x = evalTermStrict(defs.js, location, binding, value);
      is.set(id, x, location);
      console.log(":::", id, x);
      return [mkRest(binding)];
    default:
      throw "";
  }
}

const mainProgram = `
node _ id --- node id.

succeeds I I' --- old I.
node I, body I _ S, @lt 0 @length(S), old I -> 0 --- tip I.
tip I --- contains-tip I.
contains I I', contains-tip I' --- contains-tip I.
#tip I, contains-tip I -> 0 --- can-advance I.

############## Updates ##############

###  Rule Activation

node-tag I T, rule name T 'during Body, @initBranch name Body L
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
node I', contains I I', body I' {} Body, label I' L.

1 = 2, node-tag I T, rule name T 'after Body, @initBranch name Body L
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
@foo.

### Branch Update

force x L B --- force x L B {}.

!force x L BindPattern Choice, label I L, tip I, contains P I,
body I B S, @le BindPattern B, @updateBranch P I L B S Choice L' B' S'
>>>
node I', body I' B' S', label I' L', succeeds I I', contains P I'.

# prune this tip
!terminate x L, label I L, tip I >>> succeeds I _.

node I, tip I --- max-tip -> I.

# Diagnostic
tip I, label I L, body I B S, contains P I --- z I P L B S.

label I 'stuck, succeeds I' I, body I' _ S --- stuck I S.
`;

let relTypes = {
  located: "last",
  owner: "last",

  delay: "max",
  "next-delay": "min",
  "max-tip": "max",
  range: "min",

  steps: "num",
  forceSteps: "num",
  energy: "num",
  "card-plays": "num",
};
function mainTest(stories, userRules) {
  let derivations = parseRules(mainProgram);

  let tr = (x) => x.map((x) => [...x, _true]);
  let single =
    (fn) =>
    (...args) =>
      tr([fn(...args)]);

  function tor(fn) {
    return (...args) => (fn(...args) ? [[...args]] : []);
  }

  let leFn = (a, b) => {
    if (a.tag === "bind") return a.value.le(b.value);
    assert(["int", "sym"].includes(a.tag));
    return a.value <= b.value;
  };
  let js = {
    _is: is, // todo !!!
    log: (...args) => {
      console.log("!!!!!!!!!! ", ...args);
    },
    initBranch: single(initBranch),
    updateBranch: (...args) => updateBranchStuck(ec, ...args),
    add: ({ value: a }, { value: b }) => mkInt(a + b),
    _eq: tor((a, b) => {
      return valEqual(a, b);
    }),
    eq: valUnify,
    lt: tor((a, b) => {
      return a.value < b.value;
    }),
    le: tor(leFn),
    gt: tor((b, a) => a.value < b.value),
    ge: tor((b, a) => leFn(a, b)),
    length: (a) => mkInt(a.value.length),
    story: ({ value: { body } }) => {
      return mkBox(body);
    },
    nonemptyBody: tor(({ value: { body } }) => {
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
  mkRootNode(state);

  /* Execute log of actions */
  // prettier-ignore
  let thelog = [
    go(2, " >>> force _ 'setup {}."), // 8
      go(4, " >>> force _ 'place-presence {} {L: 1}."), //
    go(6, " >>> force _ 'deal {}."), // 5
      go(5, " >>> force _ 'mk-card {}."), // 5

    // test misc.
    go(1, " >>> force _ 'foo {}."), //
      go(2, " >>> force _ 'push {} {L:2}."), // 2
        go(3, " >>> force _ 'move {}."), // 3
    go(1, " >>> force _ 'foo {}."), //
      go(1, " >>> force _ 'foo/a {}."), // 1
      go(1, " >>> force _ 'foo/b {}."), // 1
    go(8, " >>> force _ 'foo {}."), // 7
      go(2, " >>> force _ 'bar {}."), // 7

    go(1, " >>> force _ 'turn1 {}."),
    go(1, " >>> force _ 'turn {}."), // 6
    go(2, " >>> force _ 'spirit-phase {}."), // 2
      go(2, " >>> force _ 'spirit-grow {}."), // 2
        go(2, " >>> force _ 'deal-cards {} {}."), // 2
          go(3, " >>> force _ 'deal-cards/1 {} {}."), // 3
            go(3, " >>> force _ 'move {} {}."), // 3
        go(1, " >>> force _ 'deal-cards {} {}."), // 1
        go(2, " >>> force _ 'choose-card {} {}."), //
          go(4, " >>> force _ 'choose-card/1 {} {Name: 'call}."), //
          go(3, " >>> force _ 'move {} {}."), // 3
        go(1, " >>> force _ 'choose-card {} {}."), //
          go(4, " >>> force _ 'choose-card/1 {} {Name: 'call}."), //
            go(3, " >>> force _ 'move {} {}."), // 3
    go(1, " >>> force _ 'spirit-phase {}."), // 2
      go(10, " >>> force _ 'play-cards {}."), // 9
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
      go(3, " >>> force _ 'target-power {} {}."), //
      go(2, " >>> force _ 'activate-power {} {}."), //
    () => 'done',
  ];
  timeFn(() => ec.solve());
  let i = 0;
  function runLog() {
    while (thelog.length > 0) {
      let [t, ...rest] = thelog;
      thelog = rest;
      console.log("iter:", ++i);
      if (timeFn(t) === "done") break; // early exit
    }
    print();
  }

  runLog();

  function stepLog() {
    if (thelog.length === 0) {
      console.log("done");
      return;
    }
    let [t, ...rest] = thelog;
    timeFn(t);
    thelog = rest;
    print();
  }

  ["keydown", "onclick"].forEach((ty) => {
    window.addEventListener(ty, () => {
      stepLog();
    });
  });

  /* finish */
  function print() {
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
    ec.print(omit);
    console.log("db.size: ", state.dbAggregates.size()); // 1426 390
    console.log(state);
  }
}

function mainFoo() {
  let b = new Binding();
  function tp(o) {
    return episode.tip(tip.mk(b, o));
  }
  let turn = operation.do("turn", []);
  let done = episode.done();
  let es = [
    episode.done(),
    tp(turn),
    episode.branch(Actor.seq, []),
    episode.branch(Actor.seq, { a: episode.done() }),
    episode.branch(Actor.seq, { a: tp(turn) }),
    episode.branch(Actor.any, { a: tp(turn), b: tp(turn) }),
    episode.branch(Actor.any, { a: done, b: tp(turn) }),
    episode.branch(Actor.all, { a: done, b: tp(turn) }),
  ];
  // 5x true false 2x true
  for (let e of es) {
    //console.log(JSON.stringify(e), episodeDone(e));
    console.log(e.canonical());
    //console.log(JSON.stringify(e), e.canonical());
  }
}

let mkjs = (ec) => {
  let single =
    (fn) =>
    (...args) =>
      tr([fn(...args)]);

  function tor(fn) {
    return (...args) => (fn(...args) ? [[...args]] : []);
  }

  let leFn = (a, b) => {
    if (a.tag === "bind") return a.value.le(b.value);
    assert(["int", "sym"].includes(a.tag));
    return a.value <= b.value;
  };
  return {
    //_is: is, // todo !!!
    log: (...args) => {
      console.log("!!!!!!!!!! ", ...args);
    },
    initBranch: single(initBranch),
    updateBranch: (...args) => updateBranchStuck(ec, ...args),
    add: ({ value: a }, { value: b }) => mkInt(a + b),
    _eq: tor((a, b) => {
      return valEqual(a, b);
    }),
    eq: valUnify,
    lt: tor((a, b) => {
      return a.value < b.value;
    }),
    le: tor(leFn),
    gt: tor((b, a) => a.value < b.value),
    ge: tor((b, a) => leFn(a, b)),
    length: (a) => mkInt(a.value.length),
    story: ({ value: { body } }) => {
      return mkBox(body);
    },
    nonemptyBody: tor(({ value: { body } }) => {
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
};

let chk = (e) => console.log(JSON.stringify(e, null, 2));
function drive(prog, e) {
  let gas = 100;
  let steps = 0;
  while (steps++ < gas && canonicalEpisode(e) && !episodeDone(e)) {
    e = processInput(prog, null, filterDone(e), {});
    prog.ec.solve();
    chk(e);
  }
  chk(filterDone(e));
  console.log("steps: ", steps);
  if (steps >= gas) throw "ran out of gas";
  return e;
}

//window.onload = () => loadRules(main);
window.onload = () =>
  loadSeveral(["new.part"], ([t]) => {
    let rules = parseProgram(t);
    console.log(t);

    /* begin */
    var js = {};
    let ec = mkSeminaive([], js, relTypes);
    Object.assign(js, mkjs(ec));
    ec.init();

    let e = newEpisode("game", rules.during);
    e = timeFn(() => drive({ ec, rules }, e));
    print();
    return;
    function print() {
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
      ec.print(omit);
      console.log("db.size: ", ec.getState().dbAggregates.size()); // 1426 390
    }
  });
