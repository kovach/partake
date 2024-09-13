import {
  parseQuery,
  unrename,
  joins,
  joinTuples,
  dbOfList,
  selectTuples,
  selectTuplesWithSource,
  dbAddTuple,
  af,
  str,
  clone,
} from "./join.js";

import * as d from "./dom.js";

import grammar from "./grammar.js";

let debugSteps = false;
let debugResult = false;
let debugIterTag = true;

// Create a Parser object from our grammar.

function parse(str) {
  let parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
  parser.feed(str);
  let result = parser.results;
  if (result.length > 0) return result[0];
  return null;
}

//console.log(JSON.stringify(parse("foo X Y, baz z, bar")));
//console.log(JSON.stringify(parse("bar, after (foo X, bar Y)")));
//console.log(JSON.stringify(parse("bar, before (x), after (foo X, bar Y)")));

function mkContext(binding) {
  return { binding, del: [], add: [] };
}
function matchRule(rule, tuples) {
  let { name, guard, body } = rule;
  let db = dbOfList(tuples);
  let bindings = af(selectTuples(db, guard));
  return { name, contexts: bindings.map(mkContext), lines: body };
}
function matchRules(rules, tuples) {
  let result = [];
  for (let rule of rules) {
    let { name, contexts, lines } = matchRule(rule, tuples);
    if (contexts.length > 0) {
      lines.reverse().forEach((operations) => {
        result.push(mkLine({ name, initial: true, contexts, operations }));
      });
    }
  }
  return result;
}

function makeTuple(binding, pattern) {
  let [tag, atoms] = pattern;
  return [tag, unrename(binding, atoms)];
}

function stepOperation(db, contexts, operation) {
  function* iter(cs, fn) {
    for (let c of cs) {
      for (let [t, vals] of selectTuplesWithSource(db, operation.pattern)) {
        let v = fn(c, vals, t);
        if (v) yield v;
      }
    }
  }
  function doRel(c, t) {
    let binding = joinTuples(c.binding, t);
    if (binding) {
      return { binding, del: c.del, add: c.add };
    }
  }
  function doBeforeRel(c, vals, t) {
    let binding = joinTuples(c.binding, vals);
    if (binding) {
      return { binding, del: c.del.concat([t]), add: c.add };
    }
  }
  let result = [];
  switch (operation.tag) {
    case "rel":
      for (let c of iter(contexts, doRel)) result.push(c);
      break;
    case "before":
      for (let c of iter(contexts, doBeforeRel)) result.push(c);
      break;
    case "after":
      for (let { binding, del, add } of contexts) {
        result.push({
          binding,
          del,
          add: add.concat([makeTuple(binding, operation.pattern)]),
        });
      }
      break;
    case "subQuery":
      for (let c of contexts) {
        let { name, body } = operation;
        let choices = joins(db, body, c);
        c.binding[name] = choices;
        result.push(c);
      }
      break;
    case "take-choice":
      break;
    default:
      throw ["undefined tag stepOperation", operation];
  }
  if (debugSteps) console.log("    result: ", JSON.stringify(result));
  return result;
}
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
function unionContexts(contexts) {
  let del = [];
  let add = [];
  for (let { del: d, add: a } of contexts) {
    for (let t of d) del.push(t);
    for (let t of a) add.push(t);
  }
  return { del, add };
}

let stepLimit = 200;
function fixStack(db, rules, stack, trace) {
  let count = 0;
  while (stack.length > 0 && count++ < stepLimit) {
    let obj = stack.pop();
    if (debugIterTag) console.log(obj.tag);
    switch (obj.tag) {
      case "newTuples":
        stack = stack.concat(matchRules(rules, obj.value));
        break;
      case "line":
        let { name, initial, contexts, operations } = obj.value;
        if (initial) trace.push({ db: clone(db), name });
        if (operations.length > 0) {
          let op = operations[0];
          operations = operations.slice(1);
          stack.push(
            mkLine({
              contexts: stepOperation(db, contexts, op),
              operations,
              initial: false,
              name,
            })
          );
        } else {
          if (debugResult)
            console.log("    result: ", JSON.stringify(contexts));
          let { del, add } = unionContexts(contexts);
          for (let [tag, tuple] of del) dbAddTuple(db, tag, tuple, -1);
          for (let [tag, tuple] of add) dbAddTuple(db, tag, tuple, +1);
          if (add.length > 0) stack.push(mkNewTuples(add));
          renderDb(db);
        }
        break;
      default:
        throw ["undefined tag fixStack", obj];
    }
  }
  trace.push({ db: clone(db), name: "end" });
}

let choice = {
  tag: "choose",
  quantifierType: ["equal", 1],
  body: parseQuery("token t, in t l"),
};

let app;
function renderDb(db) {
  if (app) d.remove(app);
  app = d.createChildId("div", "left");
  //app.style.fontSize = "16pt";
  for (let [tag, rel] of db.entries()) {
    for (let [value, _] of rel.values()) {
      //console.log(`(${tag} ${value.join(" ")})`);
      let e = d.createChildElem("div", app);
      e.innerHTML = `(${tag} ${value.join(" ")})`;
    }
  }
}
function renderTraceEntry({ name, db }) {
  let e = d.createChildId("div", "right");
  e.innerHTML = name;
  e.onmouseover = () => {
    renderDb(db);
  };
}

let parseGuard = (x) => parseQuery(x)[0];
let db;
function resetDb() {
  db = dbOfList([
    ["land", [0]],
    ["land", [1]],
    ["adjacent", [0, 1]],
    ["adjacent", [1, 0]],
    ["token", [2]],
    ["in", [2, 0]],
  ]);
}
let rule1 = {
  guard: parseGuard("in t l"),
  body: [parse("after(moved t)")],
  name: "moved",
};

window.onload = () => {
  let contexts = [mkContext({})];
  let operations = parse(
    "land x, token t, before (in t x), adjacent x y, after (in t y)"
  );
  console.log(str(operations));

  console.log("~~~~~~~~~~~");
  resetDb();
  let trace = [];
  fixStack(
    db,
    [rule1],
    [mkLine({ name: "todo", initial: true, contexts, operations })],
    trace
  );
  console.log("~~~~~~~~~~~");
  fixStack(
    db,
    [rule1],
    [mkLine({ name: "todo", initial: true, contexts, operations })],
    trace
  );
  for (let entry of trace) {
    renderTraceEntry(entry);
  }
};

/* plan

dom representation of DB at all times
  with views of entries
dom representation of binding
binding picker for each quantifier type
log of rule matches, choices
  new tuples highlighted
scrub history

implement choose

dynamic game log

rule parser

*/
