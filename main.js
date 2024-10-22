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
  ppQuery,
  ppTerm,
} from "./join.js";

import { assert, ArrayMap } from "./collections.js";

import * as d from "./dom.js";
import { s } from "./dom.js";

import grammar from "./grammar.js";

let debugSteps = false;
let debugResult = false;
let debugIterTag = true;

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
  let [tag, atoms] = pattern;
  return [tag, unrename(js, binding, atoms)];
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

function dbOfPath(path) {
  let db = dbOfList([].concat(...path[mapMaybe]((node) => node.tuples)));
  return db;
}
function updateTipById(program, root, id, data) {
  return updateEvent(root, [], id, updateTip[ap](program, data));
  //return updateEvent(root, [], id, updateTip[ap](program)[ap](data));
}
function updateTip({ rules, js }, data, tip, path) {
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
    case "subquery": {
      let { query, name, rest } = episode;
      let db = dbOfPath(path);
      for (let c of context) {
        c.binding[name] = af(evalQuery(db, js, query, [c]));
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
    case "do": {
      //assert(episode.name);
      return mkCompositeEvent({
        //name: "do",
        value: context.map((binding) =>
          beginEvent(rules, substituteEventExpr(js, binding, episode.value))
        ),
      });
    }
    case "done": {
      return mkCompositeEvent({ value: [] });
    }
    default:
      throw "";
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
      tuples = tuples.map((t) => makeTuple(js, binding.binding, t));
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

function eventCompleted(event) {
  // todo
  return (
    (event.tag === "concurrent" && event.value.length === 0) ||
    (event.tag === "primitive" && event.value.length === 0)
  );
}

function reduceEvent(event) {
  let options = [];
  event = go(event, options);
  return [event, options];

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

function renderButton(content, { enter, exit, action, context }) {
  let e = d.create("div");
  e.innerHTML = content;
  e.onmouseenter = () => {
    e.classList.add("hl");
    if (enter) enter();
    if (context) context.forEach((e) => e.classList.add("hl"));
  };
  e.onmouseleave = () => {
    e.classList.remove("hl");
    if (exit) exit();
    if (context) context.forEach((e) => e.classList.remove("hl"));
  };
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

// episode := { tag: ('concurrent' | 'tip'), value: Array episode, ?next: () -> episode, ?tuples: db }
function renderEpisode(root, ep) {
  let { tag } = ep;
  switch (tag) {
    case "concurrent": {
      return createEpisodeElem(ep.name, ep.value.map(renderEpisode[ap](root)));
    }
    case "tip": {
      return d.withClass(renderTip(root, ep), "margin");
    }
    default:
      throw "";
  }
}

function renderTip({ action }, tip) {
  let { episode, context } = tip;
  switch (episode.tag) {
    case "choose":
      let e = d.create("div");
      let sets = new Map();
      for (let c of context) {
        e.appendChild(
          renderChoices(
            (b) => d.createText(ppBinding(b.binding)),
            c.binding["_choices"],
            (set) => {
              sets.set(c, set);
              // join after all choices made
              if (sets.size === tip.context.length) {
                let data = [];
                for (let v of sets.values()) {
                  data.push(...Array.from(v));
                }
                action(tip, data);
              }
            }
          )
        );
      }
      return d.flex("row", e, d.createText(","), d.createText(ppEpisode(episode.rest)));
    default:
      return renderButton(ppTip(tip), { action: () => action(tip, null) });
  }
}

function ppTip(tip) {
  return `${ppEpisode(tip.episode)} | ${tip.context
    .map((b) => ppBinding(b.binding))
    .join("; ")}`;
}
function ppEpisode(e) {
  switch (e.tag) {
    case "observation": {
      return `${ppQuery([e.pattern])}, ${ppEpisode(e.rest)}`;
    }
    case "choose": {
      let { actor, quantifier, rest } = e;
      return `${actor} chooses ${quantifier}, ${ppEpisode(rest)}`;
    }
    case "do": {
      return `do ${ppEvent(e.value)}`;
    }
    case "done": {
      return "done";
    }
    case "subquery": {
      let { query, name, rest } = e;
      return `${name} := ?(${ppQuery(query)}), ${ppEpisode(rest)}`;
    }
    case "with-tuples": {
      return `[${ppEpisode(e.body)} | ${ppQuery(e.tuples)}]`;
    }
    default:
      throw "";
      return "todo";
  }
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

function newMain() {
  let pe = parseNonterminal[ap]("episode_expr");
  let e = toTag(pe); // ([str]) => pe(str);

  let programText = `
game: do [turn | land a, land b, spirit c,
  card x, cost x 1, green x 1, red x 1,
  card y, cost y 2, blue y 2, red y 1
  ].
turn: spirit S, do [grow | the-spirit S].
turn: land L, do [defend | the-land L].
grow: the-spirit S,
  S chooses 1 ?(card c), done.
defend: the-land L, done.
turn -> do turn.
`;

  let programText2 = `
game: do [turn | land a, land b, spirit c,
  card x, cost x 1, green x 1, red x 1,
  card y, cost y 2, blue y 2, red y 1
  ].
turn: land S, S chooses 1 ?(card C), cost C Cost, done.
`;

  let ev, options;
  let rules = parseProgram(programText);
  let db = emptyDb();
  // todo
  dbAddTuple(db, "land", [freshId()], +1);
  dbAddTuple(db, "land", [freshId()], +1);
  dbAddTuple(db, "spirit", [freshId()], +1);
  let program = { rules, db, js: {} };
  ev = mkEventByName(rules, "game");
  //ev = mkTip(e`do game`);

  let app;

  function updateTipAction(tip, data) {
    ev = updateTipById(program, ev, tip.id, data);
    updateUI();
  }
  function updateUI() {
    [ev, options] = reduceEvent(ev);
    console.log(options.length);
    if (app) d.remove(app);
    app = d.createChildId("div", "log");

    if (ev) d.childParent(renderEpisode({ action: updateTipAction }, ev), app);
    d.childParent(d.renderJSON(options), app);
  }

  let log = d.getId("log");

  let x = d.childParent(d.flex("row"), log);
  updateUI();
}

window.onload = newMain;

function renderChoices(renderer, set, k) {
  let m = new Map();
  for (let v of set) {
    m.set(v, renderer(v));
  }
  return renderSubsetSelector(m, () => true, k);
}

function withMouseHighlight(elem) {
  elem.onmouseenter = () => {
    elem.classList.add("hl");
  };
  elem.onmouseleave = () => {
    elem.classList.remove("hl");
  };
  return elem;
}

// map from object to element
// render elements
function renderSubsetSelector(map, hasValidExtension, k) {
  let e = d.create("div");
  let chosen = new Set();
  for (let [term, elem] of map) {
    d.childParent(elem, e);
    elem = withMouseHighlight(elem);
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
    done.classList.add("selection");
    k(chosen);
  };
  d.childParent(done, e);
  return e;
}

/* todo now
before/after
  new binding class
basic ui work
  board: visualize entire db
choice
  quantifiers
actors
  player, default, random
count. not, comparisons

? draw episodes in progress
*/

/* later plan
mouseenter tuple -> highlight icons
declarative ui
  land l, token t, in t l
    just handle with parents
value/dynamic breakpoint?
default actions (handle unique choice)
*/
