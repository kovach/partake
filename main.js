import {
  unrename,
  dbOfList,
  dbAddTuple,
  af,
  str,
  clone,
  emptyDb,
  dbContains,
  evalQuery,
  evalTerm,
  freshId,
  valEqual,
  emptyBinding,
} from "./join.js";

import { assert, ArrayMap } from "./collections.js";

import * as d from "./dom.js";
import { s } from "./dom.js";

import grammar from "./grammar.js";

let debugSteps = false;
let debugResult = false;
let debugIterTag = true;

let ap = Symbol("partial-apply");
Function.prototype[ap] = function (e) {
  return (...args) => this.apply(this, [e].concat(args));
};
function toTag(f) {
  return ([str]) => f(str);
}
function arrayUpdate(arr, f) {
  for (let i = 0; i < arr.length; i++) {
    arr[i] = f(arr[i]);
  }
  return arr;
}
// implement early exit behavior
function forEach(arr, f) {
  for (let i = 0; i < arr.length; i++) {
    if (f(arr[i], i)) return true;
  }
  return false;
}

// Create a Parser object from our grammar.

// let parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar), {
//   keepHistory: true,
// });
function parseNonterminal(nt, text) {
  let g = nearley.Grammar.fromCompiled(grammar);
  g.start = nt;
  let parser = new nearley.Parser(g);
  parser.feed(text);
  let result = parser.results;
  assert(result.length > 0);
  return result[0];
}
let parseLine = (str) => parseNonterminal("line", str);
let parse = (str) => parseNonterminal("rule", str);
let parseRules = (str) => parseNonterminal("program", str);

//console.log(JSON.stringify(parseNonterminal("literal", "foo(x, y)")));
//console.log(JSON.stringify(parse("bar, after (foo X, bar Y)")));
//console.log(JSON.stringify(parse("bar, before (x), after (foo X, bar Y)")));

function mkNewTuples(value) {
  return {
    tag: "newTuples",
    value,
  };
}
function mkLine(value) {
  return {
    tag: "line",
    value,
  };
}

function mkTrace(db) {
  let trace = { entries: [] };
  trace.push = (entry) => {
    renderDb(db);
    renderTraceEntry(entry);
    trace.entries.push(entry);
  };
  return trace;
}

// Operation related constructors
function mkContext(binding) {
  return { binding, del: [], add: [] };
}

function matchRule(js, rule, tuples) {
  let { name, guard, body } = rule;
  let db = dbOfList(tuples);
  let bindings = af(evalQuery(db, js, guard));
  return {
    name,
    contexts: bindings.map(({ binding }) => mkContext(binding)),
    lines: body,
  };
}
function matchRules(js, rules, tuples) {
  let result = [];
  for (let rule of rules) {
    let { name, contexts, lines } = matchRule(js, rule, tuples);
    if (contexts.length > 0) {
      lines.reverse().forEach((operations) => {
        result.push(mkLine({ name, contexts, operations, ruleText: rule.ruleText }));
      });
    }
  }
  return result;
}

function makeTuple(js, binding, pattern) {
  let [tag, atoms] = pattern;
  return [tag, unrename(js, binding, atoms)];
}

function stepOperation(db, js, contexts, operation) {
  function* iter_(cs, fn) {
    for (let base of cs) {
      // todo: thread del/add through evalQuery
      for (let binding of evalQuery(
        db,
        js,
        [operation.pattern],
        [{ binding: base.binding, used: [] }]
      )) {
        let v = fn(binding, base);
        if (v) yield v;
      }
    }
  }
  let doRel = ({ binding }, { del, add }) => ({ binding, del, add });
  let doBeforeRel = ({ binding, used }, { del, add }) => {
    del.push(used[0]);
    return {
      binding,
      del,
      add,
    };
  };

  let result = [];
  switch (operation.tag) {
    case "rel":
      for (let c of iter_(contexts, doRel)) result.push(c);
      break;
    case "before":
      for (let c of iter_(contexts, doBeforeRel)) result.push(c);
      break;
    case "after":
      for (let { binding, del, add } of contexts) {
        add.push(makeTuple(js, binding, operation.pattern)); // modifies binding
        result.push({
          binding,
          del,
          add,
        });
      }
      break;
    // generated by parser for `choose` with `_choices` as the name
    case "subQuery":
    case "countQuery":
      for (let c of contexts) {
        let { name, body } = operation;
        let choices = af(evalQuery(db, js, body, [{ binding: c.binding, used: [] }]));
        if (operation.tag === "subQuery") c.binding[name] = choices;
        else if (operation.tag === "countQuery") c.binding[name] = choices.length;
        else throw "unreachable";
        result.push(c);
      }
      break;
    case "applyChoices":
      for (let { binding, del, add } of contexts) {
        for (let b of binding._choices) {
          b = structuredClone(b);
          result.push({ binding: b, del, add });
        }
      }
      break;
    case "binOp":
      let fn;
      if (operation.operator === "<") fn = (a, b) => a < b;
      else if (operation.operator === "=") fn = (a, b) => a === b;
      else throw "unimplemented operator";
      for (let context of contexts) {
        let l = evalTerm(js, context.binding, operation.l);
        let r = evalTerm(js, context.binding, operation.r);
        if (fn(l, r)) result.push(context);
      }

      break;
    case "call":
      for (let c of contexts) {
        evalTerm(js, c.binding, operation.value);
        result.push(c);
      }
      break;
    case "takeChoice":
      throw "unreachable: `takeChoice` is handled by fixStack";
    default:
      throw ["undefined tag stepOperation", operation];
  }
  if (debugSteps) console.log("    result: ", JSON.stringify(result));
  return result;
}

let stepLimit = 200;
function fixStack(db, rules, js, trace, stack) {
  function unionContexts(contexts) {
    let del = [];
    let add = [];
    for (let { del: d, add: a } of contexts) {
      for (let t of d) del.push(t);
      for (let t of a) add.push(t);
    }
    return { del, add };
  }

  let count = 0;
  loop: while (stack.length > 0 && count++ < stepLimit) {
    let obj = stack.pop();
    if (debugIterTag) console.log(obj.tag);
    switch (obj.tag) {
      case "newTuples":
        let matches = matchRules(js, rules, obj.value);
        stack = stack.concat(matches);
        if (debugSteps) console.log("    matches: ", str(matches));
        break;
      case "line":
        let { name, ruleText, contexts, operations } = obj.value;
        if (operations.length > 0) {
          let op = operations[0];
          operations = operations.slice(1);
          if (op.tag === "takeChoice") {
            // todo: other quantifiers
            contexts = contexts.filter((c) => c.binding._choices.length > 0);
            trace.push({
              tag: "choice",
              type: "one",
              db,
              rules,
              trace,
              stack,
              js,

              contexts,
              operations,
              name,
              ruleText,
            });
            return;
          } else {
            stack.push(
              mkLine({
                contexts: stepOperation(db, js, contexts, op),
                operations,
                ruleText,
                name,
              })
            );
          }
        } else {
          if (debugResult) console.log("    result: ", JSON.stringify(contexts));
          let { del, add } = unionContexts(contexts);
          for (let [tag, tuple] of del) dbAddTuple(db, tag, tuple, -1);
          for (let [tag, tuple] of add) dbAddTuple(db, tag, tuple, +1);
          if (add.length > 0) stack.push(mkNewTuples(add));
          trace.push({ tag: "record", db: clone(db), name, ruleText });
        }
        break;
      default:
        throw ["undefined tag fixStack", obj];
    }
  }
}

// todo
//let elementWatchLists = new ArrayMap();
//function removeTuple(db, tag, tuple) {
//  dbAddTuple(db, tag, tuple, -1);
//  for (let e of elementWatchLists.get(key([tag, tuple]))) {
//    d.remove(e);
//  }
//}

function ppTerm(term) {
  switch (term.tag) {
    case "sym":
      return `'${term.value}`;
    case "int":
      return `${term.value}`;
  }
  throw "unreachable";
}

function ppTuple(tag, tuple) {
  tuple = tuple.map(ppTerm);
  let tupleText = tuple.join(" ");
  return `(${tag}${tupleText.length > 0 ? " " + tupleText : ""})`;
}
function ppBinding(binding) {
  let pairs = [];
  for (let key in binding) {
    if (key[0] !== "_") pairs.push(`${key}: ${ppTerm(binding[key])}`);
  }
  return `{${pairs.join(", ")}}`;
}

let app;
let valRefs;
let tupleRefs;
function renderDb(db, previous) {
  if (app) d.remove(app);
  valRefs = new ArrayMap();
  tupleRefs = new ArrayMap();
  app = d.createChildId("div", "left");
  for (let [tag, rel] of db.entries()) {
    for (let [value, _] of rel.values()) {
      //console.log(`(${tag} ${value.join(" ")})`);
      let e = d.createChild("div", app);
      e.innerHTML = ppTuple(tag, value);
      if (previous) {
        if (!dbContains(previous, tag, value)) {
          e.classList.add("hl");
        }
      }
      for (let v of value) valRefs.add(v, e);
      tupleRefs.add(str([tag, value]), e);
    }
  }
}

let globalChoiceState = {};
let elementDbMap = new Map();
function renderTraceEntry(entry) {
  switch (entry.tag) {
    case "choice":
      globalChoiceState.states = new Map();
      globalChoiceState.entry = entry;
      globalChoiceState.elements = [];
      for (let context of entry.contexts) {
        let contextChoiceState = { type: "one", chosen: new Set() };
        globalChoiceState.states.set(context, contextChoiceState);
        renderContextChoices(context);
      }
      break;
    case "record":
      let { name, ruleText, db } = entry;
      let e = d.createChildId("div", "right");
      e.innerHTML = name;
      elementDbMap.set(e, db);
      e.onmouseenter = () => {
        let prevDb = e.previousSibling ? elementDbMap.get(e.previousSibling) : emptyDb();
        renderDb(db, prevDb, e);
        d.getId("rule").innerHTML = ruleText;
      };
      break;
  }
}
function renderContextChoices(c) {
  let state = globalChoiceState.states.get(c).chosen;
  let e = d.createChildId("div", "right");
  e.innerHTML = "choose [exactly 1]:";
  c.binding._choices.forEach((o) => {
    renderChoice(state, e, o, c.binding);
  });
  globalChoiceState.elements.push(e);
}
function renderChoice(chosen, parent, { binding, used }) {
  let e = d.createChild("div", parent);
  e.innerHTML = `    ${ppBinding(binding)}`;
  e.onmouseleave = () => {
    e.classList.remove("hl");
    for (let e of d.allChildren(d.getId("left"))) {
      e.classList.remove("hl");
    }
  };
  e.onmouseenter = () => {
    for (let tuple of used) {
      for (let elem of tupleRefs.get(str(tuple))) {
        elem.classList.add("hl");
      }
    }
    e.classList.add("hl");
  };
  e.onclick = () => {
    if (chosen.has(binding)) {
      chosen.delete(binding);
      e.classList.remove("selection");
    } else {
      chosen.add(binding);
      e.classList.add("selection");
    }
    checkGlobalChoiceState();
  };
}
function checkGlobalChoiceState() {
  for (let v of globalChoiceState.states.values()) {
    if (!checkChoiceState(v)) return false;
  }
  // ready to go
  globalChoiceState.elements.forEach(d.remove);
  let { js, db, rules, trace, stack, contexts, operations, name, ruleText } =
    globalChoiceState.entry;
  for (let c of contexts) {
    c.binding._choices = Array.from(globalChoiceState.states.get(c).chosen);
  }
  operations = [{ tag: "applyChoices" }].concat(operations);
  stack.push(mkLine({ contexts, operations, ruleText, name }));
  fixStack(db, rules, js, trace, stack);
}
function checkChoiceState(state) {
  switch (globalChoiceState.entry.type) {
    case "one":
      return state.chosen.size === 1;
    default:
      throw "missing quantifier type";
  }
}

function oldMain() {
  let db = emptyDb();

  function mkRule(name, guard, ruleText) {
    return {
      guard: [parseNonterminal("relation", guard)],
      body: [parseLine(ruleText)],
      name,
      ruleText: `(${guard}): ${ruleText}`,
    };
  }

  let ruleText = `
(init): after (turn 1).
(init): after (token _).

initial-facts (init): after (
  land l1, land l2, land l3,
  adjacent l1 l2, adjacent l2 l3, adjacent l3 l2, adjacent l2 l1,

  position l1 1 1,
  position l2 1 2,
  position l3 1 3
  ).

next-turn
(turn a): after (turn !incr(a)).

place-token
(token t): choose [exactly 1] (land loc), after (in t loc).

turn-move
(turn _):
  land x, choose [exactly 1] (in t x, adjacent x y),
  before (in t x), after (in t y).

render-land (position l r c): !mkLand(l, r, c).
`;
  let rules = parseRules(ruleText);

  console.log("rules: ", rules);

  function mkInt(value) {
    return { tag: "int", value };
  }
  let js = {
    incr: (x) => {
      // todo: annoying
      return mkInt(x.value + 1);
    },
    mkLand: (id, row, column) => {
      let w = 80;
      let margin = 10;
      let padding = 10;
      let e = s.mkRectangle(
        padding / 2 + margin + (column.value - 1) * (w + padding),
        padding / 2 + margin + (row.value - 1) * (w + padding),
        w,
        w
      );
      e.setAttribute("my-id", ppTerm(id));
    },
  };

  let contexts = [mkContext({})];
  let trace = mkTrace(db);
  function go(ruleText) {
    let operations = parseLine(ruleText);
    return fixStack(db, rules, js, trace, [
      mkLine({ name: "repl", ruleText, contexts, operations }),
    ]);
  }
  go(`after(init)`);
}

function mkCompositeEvent(values) {
  return { ...values, tag: "concurrent", id: freshId() };
}
function mkPrimitiveEvent(values) {
  return { ...values, tag: "primitive", id: freshId() };
}
function isComposite(event) {
  return event.tag === "concurrent";
}

function updateTip({ rules, db, js }, tip) {
  let { value: episode, context } = tip;
  switch (episode.tag) {
    case "observation": {
      let newC = af(evalQuery(db, js, [episode.pattern], context));
      console.log(str(context));
      console.log(str(newC));
      return {
        ...tip,
        value: episode.rest,
        context: newC,
      };
    }
    case "do": {
      return mkCompositeEvent({
        value: context.map((binding) =>
          beginEvent(rules, substituteEventExpr(binding, episode.value))
        ),
      });
    }
  }
}
function substituteEventExpr(binding, expr) {
  let recurse = substituteEventExpr[ap](binding);
  switch (expr.tag) {
    case "done": {
      // todo
      return expr;
    }
    case "literal": {
      return expr;
    }
    case "concurrent": {
      let { a, b } = expr;
      return { ...expr, a: recurse(a), b: recurse(b) };
    }
    case "sequence": {
      let { a, b } = expr;
      return { ...expr, a: recurse(a), b: recurse(b) };
    }
    case "with-tuples": {
      let { tuples, body } = expr;
      // todo: apply binding to tuples
      //tuples = tuples.map((t) => unrename(js, binding.binding, t));
      return { ...expr, tuples, body: recurse(body) };
    }
  }
}
function makeTip(expr) {
  return { id: freshId(), tag: "tip", value: expr, context: [emptyBinding()] };
}
function makeEventByName(rules, name) {
  let now = rules.defs.get(name);
  let after = rules.triggers.get(name);
  let node = mkCompositeEvent({ name, value: now.map(makeTip) });
  node.next = () => mkCompositeEvent({ name: `${name}'`, value: after.map(makeTip) });
  return node;
}

// StaticEventExpr = sequence(a, b) | concurrent(a,b) | literal(name) | with-tuples(tuples, a)
function beginEvent(rules, expr) {
  let recurse = beginEvent[ap](rules);
  switch (expr.tag) {
    case "done": {
      // todo
      return mkPrimitiveEvent({ value: [] });
    }
    case "literal": {
      return makeEventByName(rules, expr.name);
    }
    case "concurrent": {
      let { a, b } = expr;
      return mkCompositeEvent({ value: [recurse(a), recurse(b)] });
    }
    case "sequence": {
      let { a, b } = expr;
      return mkCompositeEvent({ value: [recurse(a)], next: () => recurse(b) });
    }
    case "with-tuples": {
      let { tuples, body } = expr;
      return mkCompositeEvent({ value: [recurse(body)], tuples });
    }
  }
}

function eventCompleted(event) {
  // todo
  return (
    (event.tag === "concurrent" && event.value.length === 0) ||
    (event.tag === "primitive" && event.value.length === 0)
  );
}

function reduceEvent(event) {
  let options = [];
  event = reduceEvent_(event, options);
  return [event, options];
}

function reduceEvent_(event, options) {
  //console.log("visit: ", event.id, event.tag);
  switch (event.tag) {
    case "concurrent": {
      event.value = arrayUpdate(event.value, (e) => reduceEvent_(e, options)).filter(
        (x) => x
      );
      break;
    }
  }
  if (eventCompleted(event)) {
    if (event.name) console.log(`finishing ${event.name}`);
    if (event.next) return reduceEvent_(event.next(), options);
    return false;
  } else {
    if (event.tag === "tip") options.push(event);
    return event;
  }
}

// todo: find path from root to event, construct total db
function updateEvent(root, id, fn) {
  if (valEqual(root.id, id)) {
    return fn(root);
  } else if (isComposite(root)) {
    if (
      forEach(root.value, (c, i) => {
        let c_ = updateEvent(c, id, fn);
        if (c_) {
          root.value[i] = c_;
          return true;
        }
      })
    ) {
      return root;
    }
    return false;
  }
}

function updateTipById(program, root, id) {
  return updateEvent(root, id, updateTip[ap](program));
}

function renderButton(content, context, action, parent) {
  let e = d.createChild("div", parent);
  e.innerHTML = content;
  e.onmouseenter = () => {
    context.forEach((e) => e.classList.add("hl"));
    e.classList.add("hl");
  };
  e.onmouseleave = () => {
    context.forEach((e) => e.classList.remove("hl"));
    e.classList.remove("hl");
  };
  e.onclick = action;
}

function newMain() {
  let pe = parseNonterminal[ap]("episode_expr");
  let e = toTag(pe); // ([str]) => pe(str);

  let defs = new ArrayMap([
    ["turn", [e`p X, do grow`, e`do defend`]],
    ["grow", [e`do .`]],
    ["defend", [e`do .`]],
  ]);

  let triggers = new ArrayMap([
    ["turn", [e`do turn`]],
    ["grow", []],
    ["defend", []],
  ]);

  console.log("parse ep", parseNonterminal("episode_expr", "do ."));
  console.log("parse ep", parseNonterminal("episode_expr", "foo X Y, do ."));
  console.log("parse ep", e`foo X Y, bar Y Z, do (a -> b)`);
  console.log("parse ep", e`foo X Y, bar Y Z, do a, b`);
  console.log("parse ep", e`do turn`);

  let ev, options;
  let rules = { defs, triggers };
  let db = emptyDb();
  dbAddTuple(db, "p", [freshId()], +1);
  dbAddTuple(db, "p", [freshId()], +1);
  dbAddTuple(db, "q", [freshId()], +1);
  let program = { rules, db, js: {} };
  ev = makeTip(e`do turn`);

  let app;
  function updateUI() {
    [ev, options] = reduceEvent(ev);
    console.log(options.length);
    if (app) d.remove(app);
    app = d.createChildId("div", "left");
    options.forEach((o) =>
      renderButton(
        str(o),
        [],
        () => {
          console.log("click: ", o);
          ev = updateTipById(program, ev, o.id);
          updateUI();
        },
        app
      )
    );
  }
  updateUI();
}

window.onload = newMain;

/* todo now
observation
  multi-level db, fix substitute
choice
before/after
  new binding class

? draw episodes in progress
*/

/* later plan
mouseenter tuple -> highlight icons
choose any
declarative ui
  land l, token t, in t l
    just handle with parents
value/dynamic breakpoint?
default actions (handle unique choice)
*/
