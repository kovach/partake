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
} from "./join.js";

import grammar from "./grammar.js";

let debugSteps = false;
let debugResult = true;

// Create a Parser object from our grammar.

function parse(str) {
  let parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
  parser.feed(str);
  let result = parser.results;
  if (result.length > 0) return result[0];
  return null;
}

console.log(JSON.stringify(parse("foo X Y, baz z, bar")));
console.log(JSON.stringify(parse("bar, after (foo X, bar Y)")));
console.log(JSON.stringify(parse("bar, before (x), after (foo X, bar Y)")));

function mkContext(binding) {
  return { binding, del: [], add: [] };
}
function matchRule(rule, tuples) {
  let db = dbOfList(tuples);
  let bindings = af(selectTuples(db, rule.guard));
  return { contexts: bindings.map(mkContext), lines: rule.body };
}
function matchRules(rules, tuples) {
  let result = [];
  for (let rule of rules) {
    let { contexts, lines } = matchRule(rule, tuples);
    if (contexts.length > 0) {
      lines.reverse().forEach((operations) => {
        result.push(mkLine({ contexts, operations }));
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
function fixStack(db, rules, stack) {
  while (stack.length > 0) {
    let obj = stack.pop();
    console.log(obj.tag);
    switch (obj.tag) {
      case "newTuples":
        stack = stack.concat(matchRules(rules, obj.value));
        break;
      case "line":
        let { contexts, operations } = obj.value;
        if (operations.length > 0) {
          let op = operations[0];
          operations = operations.slice(1);
          stack.push(
            mkLine({
              contexts: stepOperation(db, contexts, op),
              operations,
            })
          );
        } else {
          if (debugResult)
            console.log("    result: ", JSON.stringify(contexts));
          let { del, add } = unionContexts(contexts);
          for (let [tag, tuple] of del) dbAddTuple(db, tag, tuple, -1);
          for (let [tag, tuple] of add) dbAddTuple(db, tag, tuple, +1);
          if (add.length > 0) stack.push(mkNewTuples(add));
        }
        break;
      default:
        throw ["undefined tag fixStack", obj];
    }
  }
}

let p = (x) => parseQuery(x)[0];
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
  guard: p("in t l"),
  body: [parse("after(moved t)")],
};

let contexts = [mkContext({})];
let operations = parse(
  "land x, token t, before (in t x), adjacent x y, after (in t y)"
);
console.log(str(operations));

console.log("~~~~~~~~~~~");
resetDb();
fixStack(db, [rule1], [mkLine({ contexts, operations })]);
console.log("~~~~~~~~~~~");
fixStack(db, [rule1], [mkLine({ contexts, operations })]);

let choice = {
  tag: "choose",
  quantifierType: ["equal", 1],
  body: parseQuery("token t, in t l"),
};

/* plan

dom representation of DB at all times
  with views of entries
dom representation of binding
binding picker for each quantifier type
log of rule matches, choices
  new tuples highlighted
scrub history

minimal parser

implement choose

dynamic game log

rule parser

*/
