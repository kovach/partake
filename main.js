import { assert } from "./collections.js";
import { parseNonterminal, parseProgram } from "./parse.js";
import { mkInt, mkBox, mkBind, valEqual, af, Binding, isVar } from "./join.js";
import { mkSeminaive } from "./derive.js";
import {
  Actor,
  canonUpdate,
  episode,
  episodeDone,
  filterDone,
  Input,
  intoUpdate,
  json,
  newEpisode,
  operation,
  ppe,
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

let _true = mkInt(1);
let labelSep = "/";

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

let mkjs = () => {
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
        return [[a, b, mkBind(out), _true]];
      }
      return [];
    },
  };
};

let chk = (e, str = "") => console.log(str, JSON.stringify(json(e), null, 2));

function drive(prog, e, print = true) {
  let gas = 100;
  let steps = 0;
  if (print) chk(e, "start: ");
  while (steps++ < gas && !episodeDone(e)) {
    e = filterDone(e);
    let u = canonUpdate(e);
    if (!u) break;
    e = processInput(prog, null, e, u);
    prog.ec.solve();
    if (print) chk(e);
  }
  e = filterDone(e);
  console.log("steps: ", steps - 1);
  if (steps >= gas) throw "ran out of gas";
  return e;
}

function tob(str) {
  let x = parseNonterminal("binding_expr", str);
  x = new Binding(x.value);
  return x;
}

window.onload = () =>
  loadSeveral(["new.part"], ([t]) => {
    let rules = parseProgram(t);
    console.log(t);

    /* begin */
    var js = mkjs();
    let ec = mkSeminaive([], js, relTypes);
    ec.init();

    let prog = { ec, rules };
    let e = newEpisode("game", rules.during);

    function go(e, i) {
      e = drive(prog, e, false);
      return processInput(prog, null, e, intoUpdate(i, e));
    }
    timeFn(() => {
      // {enemy} later rule first
      e = go(e, tob("{L: 1}"));
      e = go(e, tob("{L': 2}"));
      // {token}
      e = go(e, tob("{L1: 1}"));
      e = go(e, tob("{L2: 3}"));
      e = go(e, { foo1: Input.poke, foo2: Input.poke });
      //or: e = go(e, { bar1: Input.poke, bar2: Input.poke, bar3: Input.stop });
      e = go(e, { bar1: Input.poke, bar2: Input.poke });
      e = go(e, { bar3: Input.stop });
      e = go(e, { bar1: Input.poke, bar2: Input.poke });

      // always
      e = drive(prog, e, true);
      chk(e);
      prog.ec.solve();
    });

    print();
    return;
    function print() {
      ec.print([]);
      console.log("db.size: ", ec.getState().dbAggregates.size()); // 1426 390
    }
  });
