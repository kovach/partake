import {
  substitute,
  dbOfList,
  dbAddTuple,
  af,
  str,
  emptyDb,
  dbContains,
  evalTerm,
  evalQuery,
  freshId,
  valEqual,
  emptyBinding,
  ppQuery,
  ppTerm,
  ppBinding,
  ppContext,
  addDbs,
  printDb,
  mkInt,
  mkSet,
  tuplesOfDb,
  mkSym,
} from "./join.js";

import { assert, ArrayMap, DelayedMap } from "./collections.js";

import * as d from "./dom.js";

import grammar from "./grammar.js";
import { hist, randomSample } from "./random.js";

let ap = Symbol("partial-apply");
let mapMaybe = Symbol("mapMaybe");
Function.prototype[ap] = function (...given) {
  return (...args) => this.apply(this, given.concat(args));
};
Array.prototype[mapMaybe] = function (f) {
  return this.map(f).filter((x) => x);
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

function parseNonterminal(nt, text) {
  let assertAmbiguity = true;
  let g = nearley.Grammar.fromCompiled(grammar);
  g.start = nt;
  let parser = new nearley.Parser(g);
  parser.feed(text);
  let result = parser.results;
  assert(result.length > 0);
  if (assertAmbiguity) assert(result.length === 1);
  return result[0];
}
function makeTuple(js, binding, pattern) {
  let { tag, terms } = pattern;
  return [tag, substitute(js, binding, terms)];
}

function ppTuple(tag, tuple) {
  tuple = tuple.map(ppTerm);
  let tupleText = tuple.join(" ");
  return `(${tag}${tupleText.length > 0 ? " " + tupleText : ""})`;
}

let app;
let valRefs;
let tupleRefs;
function renderDb(db, parentId, previous) {
  if (app) d.remove(app);
  valRefs = new ArrayMap();
  tupleRefs = new ArrayMap();
  app = d.createChildId("div", parentId);
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

function substituteEventExpr(js, binding, expr) {
  let recurse = substituteEventExpr[ap](js)[ap](binding);
  switch (expr.tag) {
    case "done": {
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
      // may update binding:
      tuples = tuples.map((t) => makeTuple(js, binding, t));
      return { ...expr, tuples, body: recurse(body) };
    }
  }
}
function mkCompositeEvent(values) {
  return { ...values, tag: "concurrent", id: freshId() };
}
// todo: remove
function mkPrimitiveEvent(values) {
  return { ...values, tag: "primitive", id: freshId() };
}
// todo: change field episode to expr
function mkTip(expr) {
  return { tag: "tip", episode: expr, context: [emptyBinding()], id: freshId() };
}
function isComposite(event) {
  return event.tag === "concurrent";
}

function mkEventByName(rules, name) {
  let now = rules.defs.get(name);
  let after = rules.triggers.get(name);
  let node = mkCompositeEvent({ name, value: now.map(mkTip) });
  node.next = () => mkCompositeEvent({ name: `${name}'`, value: after.map(mkTip) });
  return node;
}

// expr := done | literal(name) | sequence(a, b) | concurrent(a,b) | with-tuples(a, tuples)
function beginEvent(rules, expr) {
  let recurse = beginEvent[ap](rules);
  switch (expr.tag) {
    case "done": {
      // todo
      return mkPrimitiveEvent({ value: [] });
    }
    case "literal": {
      return mkEventByName(rules, expr.name);
    }
    case "concurrent": {
      let { a, b } = expr;
      return mkCompositeEvent({ name: false, value: [recurse(a), recurse(b)] });
    }
    case "sequence": {
      let { a, b } = expr;
      return mkCompositeEvent({
        name: false,
        value: [recurse(a)],
        next: () => recurse(b),
      });
    }
    case "with-tuples": {
      let { tuples, body } = expr;
      return mkCompositeEvent({ name: false, value: [recurse(body)], tuples });
    }
  }
}

function updatePathDb(db, context) {
  context.forEach((c) => {
    c.notes.get("delete").forEach(([tag, tuple]) => dbAddTuple(db, tag, tuple, -1));
    c.notes.get("add").forEach(([tag, tuple]) => dbAddTuple(db, tag, tuple, +1));
  });
}

function updateTip({ db, rules, js }, data, tip, path) {
  function dbOfPath(path) {
    return addDbs([db, dbOfList([].concat(...path[mapMaybe]((node) => node.tuples)))]);
  }
  let binaryOperatorFunctions = {
    "<": (l, r) => l.value < r.value,
    ">": (l, r) => l.value > r.value,
    "<=": (l, r) => l.value <= r.value,
    ">=": (l, r) => l.value >= r.value,
    "=": (l, r) => (l.value = r.value),
  };
  let { episode, context } = tip;
  //renderDb(db, "right");
  switch (episode.tag) {
    case "observation": {
      let db = dbOfPath(path);
      context = af(evalQuery(db, js, [episode.pattern], context));
      return {
        ...tip,
        episode: episode.rest,
        context,
      };
    }
    case "modification": {
      let { before, after, rest } = episode;
      before = before.map((pattern) => ({ ...pattern, modifiers: ["delete"] }));
      //if (before.length > 0) throw "";
      context = af(evalQuery(db, js, before, context));
      // may modify c!
      context.forEach((c) => {
        after.forEach((pattern) => {
          c.notes.add("add", makeTuple(js, c, pattern));
        });
      });
      return {
        ...tip,
        episode: rest,
        context,
      };
    }
    case "subquery": {
      let { query, name, rest } = episode;
      let db = dbOfPath(path);
      for (let c of context) {
        c.set(name, mkSet(af(evalQuery(db, js, query, [c]))));
      }
      return {
        ...tip,
        episode: rest,
        context,
      };
    }
    case "choose": {
      let { rest } = episode;
      return {
        ...tip,
        episode: rest,
        context: data,
      };
    }
    case "count": {
      let { rest, name } = episode;
      context.forEach((c) => {
        c.set(name, mkInt(c.get(name).value.length));
      });
      return {
        ...tip,
        episode: rest,
        context,
      };
    }
    // todo: move to evalQuery
    case "binOp": {
      let { operator, l, r, rest } = episode;
      let fn = binaryOperatorFunctions[operator];
      context = context.filter((c) => {
        let vl = evalTerm(js, c, l);
        let vr = evalTerm(js, c, r);
        return fn(vl, vr);
      });
      return {
        ...tip,
        episode: rest,
        context,
      };
    }
    case "do": {
      updatePathDb(db, context);
      return mkCompositeEvent({
        value: context.map((binding) =>
          beginEvent(rules, substituteEventExpr(js, binding, episode.value))
        ),
      });
    }
    case "done": {
      updatePathDb(db, context);
      return mkCompositeEvent({ value: [] });
    }
    default:
      throw "";
  }
}

function updateTipById(program, root, id, data) {
  return updateEvent(root, [], id, updateTip[ap](program, data));
  //return updateEvent(root, [], id, updateTip[ap](program)[ap](data));
}

function eventCompleted(event) {
  // todo
  return (
    (event.tag === "concurrent" && event.value.length === 0) ||
    (event.tag === "primitive" && event.value.length === 0)
  );
}

function reduceEvent(event) {
  function go(event, options) {
    //console.log("visit: ", event.id, event.tag);
    switch (event.tag) {
      case "concurrent": {
        event.value = arrayUpdate(event.value, (e) => go(e, options)).filter((x) => x);
        break;
      }
    }
    if (eventCompleted(event)) {
      if (event.name) console.log(`finishing ${event.name}`);
      if (event.next) return go(event.next(), options);
      return false;
    } else {
      if (event.tag === "tip") options.push(event);
      return event;
    }
  }

  let options = [];
  event = go(event, options);
  return [event, options];
}

// todo: single traversal function
function pathToId(root, path, id) {
  if (valEqual(root.id, id)) {
    return path;
  } else if (isComposite(root)) {
    path = path.concat([root]);
    for (let c of root.value) {
      let c_ = pathToId(c, path, id);
      if (c_) {
        return c_;
      }
    }
    return false;
  }
}

function updateEvent(root, path, id, fn) {
  if (valEqual(root.id, id)) {
    return fn(root, path);
  } else if (isComposite(root)) {
    path = path.concat([root]);
    if (
      forEach(root.value, (c, i) => {
        let c_ = updateEvent(c, path, id, fn);
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

function withMouseHighlight(elem) {
  elem.addEventListener("mouseenter", () => {
    elem.classList.add("hl");
  });
  elem.addEventListener("mouseleave", () => {
    elem.classList.remove("hl");
  });
  return elem;
}

function renderButton(content, { enter, exit, action, context }) {
  let e = d.create("div");
  e.appendChild(content);
  //e.innerHTML = content;
  e = withMouseHighlight(e);
  e.addEventListener("mouseenter", () => {
    if (enter) enter();
    if (context) context.forEach((e) => e.classList.add("hl"));
  });
  e.addEventListener("mouseleave", () => {
    if (exit) exit();
    if (context) context.forEach((e) => e.classList.remove("hl"));
  });
  e.onclick = action;
  return e;
}

function createEpisodeElem(name, episodes) {
  if (name)
    return d.withClass(
      d.flex("column", d.createText(name), d.flex("row", ...episodes)),
      "episode"
    );
  else return d.flex("row", ...episodes);
}

function ppEvent(expr) {
  switch (expr.tag) {
    case "done": {
      return "done";
    }
    case "literal": {
      return `${expr.name}`;
    }
    case "concurrent": {
      let { a, b } = expr;
      return `(${ppEvent(a)}, ${ppEvent(b)})`;
    }
    case "sequence": {
      let { a, b } = expr;
      return `(${ppEvent(a)} -> ${ppEvent(b)})`;
    }
    case "with-tuples": {
      let { tuples, body } = expr;
      tuples = ppQuery(tuples);
      let limit = 30;
      tuples = tuples.length < limit ? tuples : tuples.slice(0, limit - 3) + "..."; // limit length 20
      return `[${ppEvent(body)} | ${tuples} ]`;
    }
  }
}
function ppQuantifier(quantifier) {
  switch (quantifier.tag) {
    case "eq":
      return `${quantifier.count}`;
    case "limit":
      return `max ${quantifier.count}`;
    case "amapLimit":
      return `~${quantifier.count}`;
  }
}
function ppEpisode(e) {
  switch (e.tag) {
    case "observation": {
      return `${ppQuery([e.pattern])}`;
    }
    case "choose": {
      let { actor, quantifier, name } = e;
      return `${ppTerm(actor)} chooses ${ppQuantifier(quantifier)} ${name}`;
    }
    case "count": {
      let { name, rest } = e;
      return `${name} := count ${name}, ${ppEpisode(rest)}`;
    }
    case "do": {
      return `do ${ppEvent(e.value)}`;
    }
    case "done": {
      return "done";
    }
    case "subquery": {
      let { query, name, rest } = e;
      return `${name} := (${ppQuery(query)})`;
    }
    case "with-tuples": {
      return `[${ppEpisode(e.body)} | ${ppQuery(e.tuples)}]`;
    }
    case "modification": {
      let { before, after } = e;
      return `(${ppQuery(before)}) ! (${ppQuery(after)})`;
    }
    case "binOp": {
      let { operator, l, r } = e;
      return `${ppTerm(l)} ${operator} ${ppTerm(r)}`;
    }
    default:
      throw "";
  }
}

function ppTip(tip) {
  return d.flex("column", d.createText(ppContext(tip.context)), ppEpisode(tip.episode));
}

// map from object to element
// render elements
function renderSubsetSelector(map, hasValidExtension, k) {
  let e = d.create("div");
  let chosen = new Set();
  for (let [term, elem] of map) {
    d.childParent(elem, e);
    elem = withMouseHighlight(elem);
    elem.classList.add("episode");
    elem.onclick = () => {
      if (chosen.has(term)) {
        chosen.delete(term);
        elem.classList.remove("selection");
      } else {
        chosen.add(term);
        if (hasValidExtension(chosen)) {
          elem.classList.add("selection");
        } else {
          chosen.delete(term);
        }
      }
    };
  }
  let done = d.create("button");
  done = withMouseHighlight(done);
  done.innerHTML = "accept";
  done.onclick = () => {
    if (k(chosen, e)) done.classList.add("selection");
  };
  d.childParent(done, e);
  return e;
}

function renderChoices(renderer, set, k) {
  let m = new Map();
  for (let v of set) {
    m.set(v, renderer(v));
  }
  return renderSubsetSelector(m, () => true, k);
}

function exprToList(expr) {
  let result = [];
  while (expr) {
    result.push(expr);
    expr = expr.rest;
  }
  return result;
}

// returns true if quantifier can be satisfied
function checkQuantifierFailure(quantifier, options) {
  switch (quantifier.tag) {
    case "eq":
      return options.length >= quantifier.count;
    case "limit":
      return true;
    case "amapLimit":
      return true;
  }
}

function checkQuantifier(quantifier, set, options) {
  switch (quantifier.tag) {
    case "eq":
      return set.size === quantifier.count;
    case "limit":
      return set.size <= quantifier.count;
    case "amapLimit":
      return (
        set.size <= quantifier.count &&
        set.size >= Math.min(options.length, quantifier.count)
      );
  }
}

function randomizeQuantifier(quantifier, options) {
  switch (quantifier.tag) {
    case "eq":
      return randomSample(options, quantifier.count);
    case "limit":
      throw "probably shouldn't be used";
    case "amapLimit":
      return randomSample(options, Math.min(options.size, quantifier.count));
  }
}

function renderTip({ action }, tip) {
  let { episode, context } = tip;

  function renderHead(expr) {
    switch (expr.tag) {
      case "choose":
        let { actor, quantifier, name } = expr;

        function getOptions(c) {
          return c.get(name).value;
        }

        // todo: should be part of updateTip
        context = context.filter((c) =>
          checkQuantifierFailure(quantifier, getOptions(c))
        );

        // handles two actors: the randomizer, or the user
        if (valEqual(actor, mkSym("rand"))) {
          return renderButton(d.createText(ppEpisode(expr)), {
            action: () => {
              let data = [];
              for (let c of context) {
                // todo: display the choice in button
                let v = randomizeQuantifier(quantifier, getOptions(c));
                data.push(...v);
              }
              action(tip, data);
            },
          });
        } else {
          let e = d.create("div");
          let sets = new Map();
          for (let c of context) {
            let options = getOptions(c);
            e.appendChild(
              renderChoices(
                (b) => d.createText(ppBinding(b)),
                options,
                (set, picker) => {
                  // returns whether choice is valid; used to update picker element
                  sets.set(c, set);
                  // join after all choices made
                  if (
                    sets.size === context.length &&
                    af(sets.values()).every((set) =>
                      checkQuantifier(quantifier, set, options)
                    )
                  ) {
                    let data = [];
                    for (let v of sets.values()) {
                      data.push(...Array.from(v));
                    }
                    action(tip, data);
                    // no need to return; element will be removed
                  }

                  if (!checkQuantifier(quantifier, set, options)) {
                    picker.classList.add("error");
                    return false;
                  } else {
                    picker.classList.remove("error");
                    return true;
                  }
                }
              )
            );
          }
          return e;
        }
      default:
        return renderButton(d.createText(ppEpisode(expr)), {
          action: () => action(tip, null),
        });
    }
  }

  return d.flex(
    "column",
    d.createText(context.map(ppBinding).join("; ")),
    d.createText("------"),
    renderHead(episode),
    d.withClass(
      d.create("div", ...exprToList(episode.rest).map((e) => d.createText(ppEpisode(e)))),
      "faint"
    )
  );
  //return renderButton(ppTip(tip), { action: () => action(tip, null) });
}

// episode := { tag: ('concurrent' | 'tip'), value: Array episode, ?next: () -> episode, ?tuples: db }
function renderState(root, ep) {
  let { tag } = ep;
  switch (tag) {
    case "concurrent": {
      return createEpisodeElem(ep.name, ep.value.map(renderState[ap](root)));
    }
    case "tip": {
      return d.withClass(renderTip(root, ep), "margin", "episode");
    }
    default:
      throw "";
  }
}

function renderWorld(tuples, app) {
  tuples = af(tuples);
  let elements = new DelayedMap();
  //console.log("!!!!!!!!!", af(tuples));

  function mk(label, s) {
    //console.log("making: ", s);
    let e = d.createText(`${label}: ${ppTerm(s)}`);
    app.appendChild(e);
    elements.set(ppTerm(s), e);
    return e;
  }

  for (let [tag, tuple] of tuples) {
    //console.log("!!!!!!!!!!!!!!!!!!!!!!!", tag, tuple);
    switch (tag) {
      case "spirit": {
        let [s] = tuple;
        d.withClass(mk(tag, s), "spirit");
        break;
      }
      case "land": {
        let [l] = tuple;
        d.withClass(mk(tag, l), "land");
        break;
      }
      case "adjacent": {
        let [a, b] = tuple;
        break;
      }
      case "located": {
        let [a, b] = tuple;
        elements.get(ppTerm(a), (a) => {
          elements.get(ppTerm(b), (b) => {
            d.childParent(a, b);
          });
        });
        break;
      }
    }
  }
}

function parseProgram(text) {
  let exprs = parseNonterminal("program", text);
  let defs = new ArrayMap();
  let triggers = new ArrayMap();
  for (let e of exprs) {
    switch (e.type) {
      case "def": {
        defs.add(e.head, e.body);
        break;
      }
      case "trigger": {
        triggers.add(e.head, e.body);
        break;
      }
      default:
        throw "";
    }
  }
  return { defs, triggers };
}

function parseExamples() {
  console.log("parse program: ", parseNonterminal("program", programText));
  console.log("parse ep", parseNonterminal("episode_expr", "do ."));
  console.log("parse ep", parseNonterminal("episode_expr", "foo X Y, do ."));
  console.log("parse ep", e`foo X Y, bar Y Z, do (a -> b)`);
  console.log("parse ep", e`foo X Y, bar Y Z, do a, b`);
  console.log("parse ep", e`do turn`);
}

function newMain(prog) {
  let pe = parseNonterminal[ap]("episode_expr");
  let e = toTag(pe); // ([str]) => pe(str);

  let programText1 = `
game: () ! (land a, land b, spirit s,
  card x, cost x 1, green x 1, red x 1,
  card y, cost y 2, blue y 2, red y 1), do turn.
turn: spirit S, do [grow | the-spirit S].
turn: land L, do [defend | the-land L].
grow: the-spirit S, S chooses 1 (card C), cost C Cost, done.
defend: the-land L, done.
turn -> do turn.
`;

  let programText2 = `
game: do [turn | land a, land b, spirit s,
  card x, cost x 1, green x 1, red x 1,
  card y, cost y 2, blue y 2, red y 1
  ].
turn: land S, S chooses 1 (card C), cost C Cost, done.
`;

  let programText3 = `
game: () ! (land a, land b, spirit s,
  card x, cost x 1, green x 1, red x 1,
  card y, cost y 2, blue y 2, red y 1), do turn.
turn: land L, spirit S, done.
`;

  let programText4 = `
game: () ! (land a, land b, land c, adjacent a b, adjacent b a, adjacent a c,
            spirit 's, spirit 't, located 's a, located 't c), do turn.
turn: spirit S, located S L,
  S chooses 1 (adjacent L L'),
  'rand chooses 1 (adjacent L L''),
  (located S L) ! (located S L'), done.
turn -> do turn.
`;

  let ev, options;
  let rules = parseProgram(prog);
  let db = emptyDb();
  let program = {
    rules,
    db,
    js: {
      add: (a, b) => mkInt(a.value + b.value),
    },
  };
  ev = mkEventByName(rules, "game");

  let app;
  let log = d.getId("log");

  function updateTipAction(tip, data) {
    ev = updateTipById(program, ev, tip.id, data);
    updateUI();
  }
  function updateUI() {
    [ev, options] = reduceEvent(ev);
    if (app) d.remove(app);
    app = d.createChild("div", log);

    if (ev) d.childParent(renderState({ action: updateTipAction }, ev), app);
    renderWorld(tuplesOfDb(db), app);
    d.childParent(d.renderJSON(options), app);
  }

  updateUI();
}

window.onload = () => {
  fetch("sf.mm")
    .then((res) => res.text())
    .then((text) => newMain(text));
};

/* todo now

eliminate done.
interface
  record trail
  undo

chooser applied to other ui elements
? `new` operation
grid
datalog?

cleanup
  fix terminology (episode/expr/tip)

count
  not, comparisons
? allow to pick invalid entities but explain why not included in query
fix "turn'" nesting
actors
  default, helper

*/

/* later plan
mouseenter tuple -> highlight icons
declarative ui
  land l, token t, in t l
    just handle with parents
value/dynamic breakpoint?
default actions (handle unique choice)
*/
