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
  uniqueInt,
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
  mkVar,
  cloneDb,
  seminaive,
  seminaiveBase,
  dbEq,
} from "./join.js";

import { assert, splitArray, ArrayMap, DelayedMap } from "./collections.js";

import * as d from "./dom.js";
import { parseNonterminal, parseProgram } from "./parse.js";
import grammar from "./grammar.js";
import { randomSample } from "./random.js";

let ap = Symbol("partial-apply");
let mapMaybe = Symbol("mapMaybe");
Function.prototype[ap] = function (...given) {
  return (...args) => this.apply(this, given.concat(args));
};
Array.prototype[mapMaybe] = function (f) {
  return this.map(f).filter((x) => x);
};

function scrollBody() {
  window.scrollTo(0, document.body.scrollHeight);
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

let valRefs;
let tupleRefs;
function renderDb(db, app, previous) {
  valRefs = new ArrayMap();
  tupleRefs = new ArrayMap();
  for (let [tag, rel] of db.entries()) {
    for (let [value, _] of rel.values()) {
      let e = app.appendChild(d.createText(ppTuple(tag, value)));
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

function substituteEpisodeExpr(js, binding, expr) {
  let recurse = substituteEpisodeExpr[ap](js, binding);
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

let branchFuture = {
  expr: (value) => ({ tag: "expr", value }),
  episode: (value) => ({ tag: "episode", value }),
};

let sequenceFuture = {
  expr: (value) => ({ tag: "expr", value }),
  episode: (value) => ({ tag: "episode", value }),
};

// todo: move expr into here?
let episode = {
  concurrent: (name, value) => ({ tag: "concurrent", id: freshId(), name, value }),
  sequence: (value, rest) => ({ tag: "sequence", id: freshId(), value, rest }),
  // todo
  localTuples: (value, tuples) => ({
    tag: "concurrent",
    id: freshId(),
    value: [value],
    tuples,
  }),
  branch: (expr, context) => ({
    tag: "branch",
    id: freshId(),
    past: [],
    value: branchFuture.expr(expr),
    context: context || [emptyBinding()],
  }),
};

function mkEpisodeByName({ defs, triggers }, name) {
  let now = defs.get(name);
  let after = triggers.get(name);
  return episode.sequence(
    episode.concurrent(name, now.map(episode.branch)),
    branchFuture.episode(episode.concurrent(null, after.map(episode.branch)))
    //branchFuture.episode(episode.concurrent(`after ${name}`, after.map(episode.branch)))
  );
}

function beginEpisode(rules, expr) {
  let recurse = beginEpisode[ap](rules);
  switch (expr.tag) {
    case "literal": {
      return mkEpisodeByName(rules, expr.name);
    }
    case "concurrent": {
      let { a, b } = expr;
      return episode.concurrent(null, [recurse(a), recurse(b)]);
    }
    case "sequence": {
      let { a, b } = expr;
      return episode.sequence(recurse(a), sequenceFuture.expr(b));
    }
    case "with-tuples": {
      let { tuples, body } = expr;
      return episode.localTuples(recurse(body), tuples);
    }
  }
}

function updatePathDb(db, context) {
  context.forEach((c) => {
    c.notes.get("delete").forEach(([tag, tuple]) => dbAddTuple(db, tag, tuple, -1));
    c.notes.reset("delete");
    c.notes.get("add").forEach(([tag, tuple]) => dbAddTuple(db, tag, tuple, +1));
    c.notes.reset("add");
  });
}

function updateBranch({ db, rules, js }, data, branch, path) {
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
  let { past, value, context } = branch;
  assert(value.tag === "expr");
  assert(value.value.length > 0);
  let [expr, rest] = splitArray(value.value);
  let newPast = past.concat([expr]);
  let newBranch = { ...branch, value: branchFuture.expr(rest), past: newPast };

  switch (expr.tag) {
    case "observation": {
      let db = dbOfPath(path);
      // these are fresh
      context = af(evalQuery(db, js, [expr.pattern], context));
      return { ...newBranch, context };
    }
    case "retract": {
      let { query } = expr;
      query = query.map((pattern) => ({ ...pattern, modifiers: ["delete"] }));
      context = af(evalQuery(db, js, query, context)); // these are fresh
      updatePathDb(db, context);
      return { ...newBranch, context };
    }
    case "assert": {
      let { tuples } = expr;
      context.forEach((c) => {
        tuples.forEach((pattern) => {
          c.notes.add("add", makeTuple(js, c, pattern));
        });
      });
      updatePathDb(db, context);
      return { ...newBranch, context };
    }
    case "subquery": {
      let { query, name } = expr;
      let db = dbOfPath(path);
      context = context.map((c) => {
        c = c.clone();
        c.set(name, mkSet(af(evalQuery(db, js, query, [c]))));
        return c;
      });
      return { ...newBranch, context };
    }
    case "choose": {
      return { ...newBranch, context: data };
    }
    case "count": {
      let { name } = expr;
      context = context.map((c) => c.clone().set(name, mkInt(c.get(name).value.length)));
      return { ...newBranch, context };
    }
    // todo: move to evalQuery
    case "binOp": {
      let { operator, l, r, rest } = expr;
      let fn = binaryOperatorFunctions[operator];
      context = context.filter((c) => {
        let vl = evalTerm(js, c, l);
        let vr = evalTerm(js, c, r);
        return fn(vl, vr);
      });
      return { ...newBranch, context };
    }
    case "subbranch": {
      let newEpisode = {
        ...newBranch,
        value: branchFuture.episode(
          episode.sequence(
            episode.branch(
              expr.branch,
              context.map((c) => c.clone())
            ),
            sequenceFuture.episode(episode.branch(rest, context))
          )
        ),
      };
      return newEpisode;
    }
    case "do": {
      if (rest.length === 0) {
        let newEpisode = {
          ...newBranch,
          value: branchFuture.episode(
            episode.concurrent(
              null,
              context.map((binding) =>
                beginEpisode(rules, substituteEpisodeExpr(js, binding, expr.value))
              )
            )
          ),
        };
        return newEpisode;
      } else {
        let newEpisode = {
          ...newBranch,
          value: branchFuture.episode(
            episode.sequence(
              episode.concurrent(
                null,
                context.map((binding) =>
                  beginEpisode(rules, substituteEpisodeExpr(js, binding, expr.value))
                )
              ),
              sequenceFuture.episode(episode.branch(rest, context))
            )
          ),
        };
        return newEpisode;
      }
    }
    case "done": {
      return {
        ...newBranch,
      };
    }
    default:
      throw "";
  }
}

function updateBranchById(program, ep, id, data) {
  return updateEpisode(ep, [], id, updateBranch[ap](program, data));
}

function updateSequenceFuture(f, path, id, fn) {
  switch (f.tag) {
    case "expr":
      return f;
    case "episode":
      return sequenceFuture.episode(updateEpisode(f.value, path, id, fn));
  }
}

// traverses whole tree looking for node matching `id`
function updateEpisode(ep, path, id, fn) {
  path = path.concat([ep]);
  switch (ep.tag) {
    case "concurrent": {
      let { value } = ep;
      return { ...ep, value: value.map((c) => updateEpisode(c, path, id, fn)) };
    }
    case "sequence": {
      let { value, rest } = ep;
      return {
        ...ep,
        value: updateEpisode(value, path, id, fn),
        rest: updateSequenceFuture(rest, path, id, fn),
      };
    }
    case "branch": {
      if (valEqual(ep.id, id)) return fn(ep, path);
      let { value } = ep;
      if (value.tag === "episode") {
        return {
          ...ep,
          value: branchFuture.episode(updateEpisode(value.value, path, id, fn)),
        };
      }
      return ep;
    }
    default:
      throw "";
  }
}

function isActive(e) {
  switch (e.tag) {
    case "concurrent": {
      let { value } = e;
      return value.some(isActive);
    }
    case "sequence": {
      let { value, rest } = e;
      return isActive(value) || (rest.tag === "episode" && isActive(rest.value));
    }
    case "branch": {
      let { value } = e;
      switch (value.tag) {
        case "expr":
          return value.value.length > 0;
        case "episode":
          return isActive(value.value);
      }
    }
    default:
      throw "";
  }
}

// The main purpose of this is to `beginEpisode` when the first part of a sequence has completed.
// The secondary purpose is to accumulate all the branches that are active into the options array.
// returns updated version of `ep` argument
function forceSequence(program, /*output:*/ options, ep) {
  let recurse = forceSequence[ap](program, options);
  switch (ep.tag) {
    case "concurrent": {
      let { value } = ep;
      return { ...ep, value: value.map(recurse) };
    }
    case "sequence": {
      let { value, rest } = ep;
      value = recurse(value);
      switch (rest.tag) {
        case "expr":
          if (!isActive(value)) {
            let { rules } = program;
            rest = sequenceFuture.episode(recurse(beginEpisode(rules, rest.value)));
          }
          break;
        case "episode":
          rest = sequenceFuture.episode(recurse(rest.value));
      }
      return { ...ep, value, rest };
    }
    case "branch": {
      let { value } = ep;
      switch (value.tag) {
        case "episode": {
          return {
            ...ep,
            value: branchFuture.episode(recurse(value.value)),
          };
        }
        case "expr": {
          if (isActive(ep)) options.push(ep);
          return ep;
        }
      }
    }
    default:
      throw "";
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
      d.flex(
        "column",
        d.withClass(d.createText(name), "bold"),
        d.flex("row", ...episodes)
      ),
      "episode"
    );
  else return d.flex("row", ...episodes);
}

function ppEpisodeExpr(expr) {
  switch (expr.tag) {
    case "literal": {
      return `${expr.name}`;
    }
    case "concurrent": {
      let { a, b } = expr;
      return `(${ppEpisodeExpr(a)}, ${ppEpisodeExpr(b)})`;
    }
    case "sequence": {
      let { a, b } = expr;
      return `(${ppEpisodeExpr(a)} -> ${ppEpisodeExpr(b)})`;
    }
    case "with-tuples": {
      let { tuples, body } = expr;
      tuples = ppQuery(tuples);
      let limit = 30;
      tuples = tuples.length < limit ? tuples : tuples.slice(0, limit - 3) + "..."; // limit length 20
      return `[${ppEpisodeExpr(body)} | ${tuples} ]`;
    }
    default:
      throw "";
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
      let { name } = e;
      return `${name} := count ${name}`;
    }
    case "do": {
      return `!do ${ppEpisodeExpr(e.value)}`;
    }
    case "done": {
      return "!done";
    }
    case "subquery": {
      let { query, name } = e;
      return `${name} := (${ppQuery(query)})`;
    }
    case "with-tuples": {
      return `[${ppEpisode(e.body)} | ${ppQuery(e.tuples)}]`;
    }
    case "binOp": {
      let { operator, l, r } = e;
      return `${ppTerm(l)} ${operator} ${ppTerm(r)}`;
    }
    case "retract": {
      let { query } = e;
      return `-(${ppQuery(query)})`;
    }
    case "assert": {
      let { tuples } = e;
      return `+(${ppQuery(tuples)})`;
    }
    case "subbranch": {
      return `(${e.branch.map(ppEpisode).join(", ")})`;
    }
    default:
      throw "";
  }
}

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
      return randomSample(options, Math.min(options.length, quantifier.count));
  }
}

// todo: move transition logic out of render!
function renderChoiceExpr(action, branch, expr) {
  let { context } = branch;
  let { actor, quantifier, name } = expr;
  function getOptions(c) {
    return c.get(name).value;
  }

  // todo: should be part of updateBranch
  context = context.filter((c) => checkQuantifierFailure(quantifier, getOptions(c)));

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
        action(branch, data);
      },
    });
  } else {
    let sets = new Map();
    return d.create(
      "div",
      ...context.map((c) => {
        let options = getOptions(c);
        return renderChoices(
          (b) => d.createText(ppBinding(b)),
          options,
          // returns whether choice is valid; used to update picker element
          (set, picker) => {
            sets.set(c, set);
            // join after all choices made
            if (
              sets.size === context.length &&
              af(sets.values()).every((set) => checkQuantifier(quantifier, set, options))
            ) {
              let data = [];
              for (let v of sets.values()) {
                data.push(...Array.from(v));
              }
              action(branch, data);
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
        );
      })
    );
  }
}

function activeBranchHeadExpr(branch) {
  return branch.value.value[0];
}

function renderBranch(action, active, branch) {
  function renderPlain(expr) {
    return d.createText(ppEpisode(expr));
  }
  function renderHead(expr) {
    switch (expr.tag) {
      case "choose":
        return renderChoiceExpr(action, branch, expr);
      default:
        return renderButton(renderPlain(expr), {
          action: () => action(branch, null),
        });
    }
  }
  function renderFuture(f) {
    switch (f.tag) {
      case "expr": {
        if (f.value.length === 0) return [];
        let [h, t] = splitArray(f.value);
        return [
          d.createText("------"),
          // active used only here
          active ? storeEpisodeElem(branch.id, renderHead(h)) : renderPlain(h),
          d.withClass(d.create("div", ...t.map(renderPlain)), "faint"),
        ];
      }
      case "episode": {
        return [renderEpisode(action, active, f.value)];
      }
      default:
        throw "";
    }
  }

  let { past, value, context } = branch;

  let pastElems =
    past.length === 0
      ? []
      : past
          .map((e) => d.withClass(renderPlain(e), "faint"))
          .concat(d.createText("------"));

  let bindingElems = context.map((c) => {
    let e = d.createText(ppBinding(c));
    return isActive(branch) ? e : d.withClass(e, "faint");
  });
  return d.flex("column", ...pastElems, ...bindingElems, ...renderFuture(value));
}

let episodeElements = new Map();
function storeEpisodeElem(id, elem) {
  episodeElements.set(id, elem);
  return elem;
}

function renderEpisode(action, active, ep) {
  function renderFuture(action, active, e) {
    switch (e.tag) {
      case "expr": {
        // cannot be active
        return d.createText(ppEpisodeExpr(e.value));
      }
      case "episode": {
        return renderEpisode(action, active, e.value);
      }
    }
  }

  switch (ep.tag) {
    case "concurrent": {
      return createEpisodeElem(ep.name, ep.value.map(renderEpisode[ap](action, active)));
    }
    case "sequence": {
      let { value, rest } = ep;
      let firstActive = isActive(value);
      return d.flex(
        "column",
        renderEpisode(action, active && firstActive, value),
        renderFuture(action, active && !firstActive, rest)
      );
    }
    case "branch": {
      return d.withClass(renderBranch(action, active, ep), "margin", "episode");
    }
    default:
      throw "";
  }
}

function mkWorldRender(tokens, containments, ignored) {
  return (tuples, app) => {
    let elements = new DelayedMap();
    function mk(label, s) {
      let e = d.createText(`${label}: ${s.map(ppTerm).join(" ")}`);
      app.appendChild(e);
      elements.set(ppTerm(s[s.length - 1]), e);
      return e;
    }
    for (let [tag, tuple] of tuples) {
      if (tokens.includes(tag)) d.withClass(mk(tag, tuple), tag);
      else if (containments.includes(tag)) {
        let [a, b] = tuple;
        elements.get(ppTerm(a), (a) => {
          elements.get(ppTerm(b), (b) => {
            d.childParent(a, b);
          });
        });
      } else if (ignored.includes(tag)) {
      } else throw "";
    }
  };
}

// todo: working tutorial examples
function parseExamples() {
  console.log("parse program: ", parseNonterminal("program", programText));
  console.log("parse ep", parseNonterminal("episode_expr", "do ."));
  console.log("parse ep", parseNonterminal("episode_expr", "foo X Y, do ."));
  console.log("parse ep", e`foo X Y, bar Y Z, do (a -> b)`);
  console.log("parse ep", e`foo X Y, bar Y Z, do a, b`);
  console.log("parse ep", e`do turn`);
}

// todo: working tutorial examples
function defunctProgramTexts() {
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
}

function newMain(rules) {
  let program = {
    rules,
    db: emptyDb(),
    js: {
      add: (a, b) => mkInt(a.value + b.value),
      sub: (a, b) => mkInt(a.value - b.value),
    },
  };

  let now = mkEpisodeByName(rules, "game");
  let options = [];
  let history = [];

  let log = d.getId("log");
  let app;

  function updateOptions() {
    options = [];
    now = forceSequence(program, options, now);
    updateUI();
  }

  function updateBranchAction(branch, data) {
    history.push({ now, db: cloneDb(program.db) });
    now = updateBranchById(program, now, branch.id, data);
    updateOptions();
  }

  let render = mkWorldRender(
    ["hand", "deck", "card", "play-area", "discard", "choose-area", "player"],
    ["located"],
    []
  );

  function updateUI() {
    if (app) d.remove(app);
    app = d.createChild("div", log);

    if (now) {
      app.appendChild(renderEpisode(updateBranchAction, true, now));

      if (options.length > 0) {
        let id = options[0].id;
        let elem = episodeElements.get(id);
        assert(elem);
        elem.classList.add("hl");
      }
    }
    render(tuplesOfDb(program.db), app);
    //d.childParent(d.renderJSON(options), app);
    console.log(options.length);
    scrollBody();
    //renderDb(program.db, app);
  }

  document.addEventListener("keydown", (ev) => {
    if (ev.key === "j") {
      if (options.length > 0) {
        // todo: allow random choice here
        if (activeBranchHeadExpr(options[0]).tag !== "choose") {
          let id = options[0].id;
          let count = 0;
          while (
            id === options[0].id &&
            activeBranchHeadExpr(options[0]).tag !== "choose"
          ) {
            updateBranchAction(options[0], null);
            count++;
          }
          console.log("!! updated ", count, " times.");
        } else console.log("click the choice!");
      } else console.log("no options");
    } else if (ev.key === "J") {
      ev.preventDefault();
      if (options.length > 0) {
        // todo: allow random choice here
        if (activeBranchHeadExpr(options[0]).tag !== "choose") {
          updateBranchAction(options[0], null);
        } else console.log("click the choice!");
      } else console.log("no options");
    } else if (ev.key === "k") {
      if (history.length > 0) {
        let past = history.pop();
        now = past.now;
        program.db = past.db;
        updateOptions();
      } else console.log("nothing to undo");
    } else if (ev.key === "r") {
      console.log("reload rules");
      loadRules((rules) => (program.rules = rules));
    } else console.log(ev);
  });

  updateOptions();
}

function loadRules(fn) {
  fetch("si.mm")
    .then((res) => res.text())
    .then((text) => fn(parseProgram(text)));
}

let unitTests = new Map([
  [
    "datalog1",
    () => {
      let rules = parseNonterminal(
        "derivation_block",
        `
adj a b --- path a b.
adj a b, path b c --- path a c.
foo X --- bar X, baz X.
bar Y --- asdf Y.`
      );
      let expected = parseNonterminal(
        "derivation_block",
        `--- adj 1 2, adj 2 3, adj 3 1,
    path 1 1, path 1 2, path 1 3,
    path 2 1, path 2 2, path 2 3,
    path 3 1, path 3 2, path 3 3.`
      );
      let db = emptyDb();
      let testDb = emptyDb();
      let newTuples = [
        { tag: "adj", tuple: [mkInt(1), mkInt(2)] },
        { tag: "adj", tuple: [mkInt(2), mkInt(3)] },
        { tag: "adj", tuple: [mkInt(3), mkInt(1)] },
      ];
      let log = d.getId("log");
      seminaive(rules, { db, js: {} }, newTuples);
      seminaiveBase(expected, { db: testDb, js: {} });
      renderDb(db, log);
      // printDb normalizes
      let result = dbEq(db, testDb);
      assert(result);
      return result;
    },
  ],
]);

function runTests() {
  for (let [key, val] of unitTests.entries()) {
    console.log(key, val());
  }
}

//window.onload = () => loadRules(main);
window.onload = runTests;

/* todo

basic datalog
  add weighted patterns to syntax
  represent/act on semiring relations
    map each tuple to a set of bindings (to support retraction)
      each rule can produce one observable result per unique binding
  timestamps?
  nonmonotone
    for each non-monotone pattern, add result to watchlist for the matched tuple
    (all edb stateful relation matches are non-monotone)

finish local db changes

actor: dom
  choice icons + run blocks

? collapse any bubble
replay
insert to db while running
  simple rule editor
header containing viz instructions
range function

? tests
? atomic rules

grid

fix highlighted choose menu
fix after turn nesting issue
? `new` operation

early exit queries that can't match
  fix "1 out of n match" visual issue

count
  not, comparisons
actors
  default (single choice, null choice), helper
? mutation inside choice
*/

/* later plan
in-game rule editor
  value breakpoints?
*/
