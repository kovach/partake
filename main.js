import {
  substitute,
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
} from "./join.js";

import { fixRules, mkProgram, emptyState, seminaive } from "./derive.js";
import { ap, assert, splitArray, ArrayMap, DelayedMap } from "./collections.js";
import * as d from "./dom.js";
import { parseNonterminal } from "./parse.js";
import { randomSample } from "./random.js";
import * as deriveTests from "./derive_tests.js";

let mapMaybe = Symbol("mapMaybe");
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

let branchFuture = {
  expr: (value) => ({ tag: "expr", value }),
  episode: (value) => ({ tag: "episode", value }),
};

let sequenceFuture = {
  expr: (value) => ({ tag: "expr", value }),
  episode: (value) => ({ tag: "episode", value }),
};

let episode = {
  concurrent: (name, value) => ({ tag: "concurrent", id: freshId(), name, value }),
  sequence: (value, rest) => ({ tag: "sequence", id: freshId(), value, rest }),
  branch: (expr, context) => ({
    tag: "branch",
    id: freshId(),
    past: [],
    value: branchFuture.expr(expr),
    context: context || [emptyBinding()],
  }),
  named: (name, db, value) => ({ tag: "named", id: freshId(), db, value }),
  // todo
  //localTuples: (value, tuples) => ({
  //  tag: "concurrent",
  //  id: freshId(),
  //  value: [value],
  //  db: dbOfList(tuples),
  //  //tuples,
  //}),
};

function mkSchema(mapping) {
  return {
    mapping,
    default: "game",
  };
}

function findHome(schema, relation) {
  let maybeHome = schema.mapping.get(relation);
  return maybeHome || schema.default;
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

//todonow
class PathDb {
  mapping = new Map();
  constructor(episodePath) {
    for (let ep of episodePath) {
      //if (ep.tag === '
    }
  }
}

function updatePathDb(db, context, path) {
  function add(tag, tuple, weight) {
    let home = findHome(schema, tag);
    let db = findDb(path, home);
    dbAddTuple(db, tag, tuple, weight);
  }

  context.forEach((c) => {
    c.notes.get("delete").forEach(([tag, tuple]) => dbAddTuple(db, tag, tuple, -1));
    c.notes.reset("delete");
    c.notes.get("add").forEach(([tag, tuple]) => dbAddTuple(db, tag, tuple, +1));
    c.notes.reset("add");
  });
}

function updateBranch({ db, rules, js }, data, branch, path) {
  function dbOfPath(path) {
    return addDbs(path[mapMaybe]((node) => node.db));
    //return addDbs([db, dbOfList([].concat(...path[mapMaybe]((node) => node.tuples)))]);
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

// todo: use this for other traversals
function traverseEpisode(fn, state, ep) {
  let rec = traverseEpisode[ap](fn, state);

  function traverseSequenceFuture(fn, f) {
    switch (f.tag) {
      case "expr":
        return f;
      case "episode":
        return sequenceFuture.episode(fn(f));
    }
  }

  function traverseBranchFuture(fn, f) {
    switch (f.tag) {
      case "expr":
        return f;
      case "episode":
        return branchFuture.episode(fn(f));
    }
  }

  switch (ep.tag) {
    case "concurrent": {
      let { value } = ep;
      return fn(state, { ...ep, value: value.map(rec) });
    }
    case "sequence": {
      let { value, rest } = ep;
      return fn(state, {
        ...ep,
        value: rec(value),
        rest: traverseSequenceFuture(rec, rest),
      });
    }
    case "branch": {
      let { value } = ep;
      return fn(state, { ...ep, value: traverseBranchFuture(value) });
    }
    default:
      throw "";
  }
}

// !! this only performs a shallow clone of episode objects and their db members.
// We rely on the update procedure generating fresh contexts/etc.
function cloneEpisode(ep) {
  return traverseEpisode(
    (_, ep) => {
      if (ep.db) return { ...ep, db: cloneDb(db) };
      else return { ...ep };
    },
    null,
    ep
  );
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

// todonow program -> rules
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

function dotExpandTerm(t) {
  switch (t.tag) {
    case "var":
    case "sym":
    case "int":
      return { prefix: [], term: t };
    case "call": {
      let { prefix, terms } = dotExpandTerms(t.args);
      return { prefix, term: { tag: "call", fn: t.fn, args: terms } };
    }
    case "dot":
      let { left, right } = t;
      //  .right case (left is null): generate a unary clause `right v`
      let prefix = [];
      let terms = [];
      // left.right case: generate a binary clause `right left v`
      let v = mkVar("?" + right + uniqueInt());
      if (left) {
        let l = dotExpandTerm(left);
        prefix = l.prefix;
        terms = [l.term];
        //v = mkVar("?" + right + uniqueInt());
      } else {
        // todo: maybe we want this semantics change
        //v = mkVar("?" + right);
      }
      terms.push(v);
      prefix.push({ tag: right, terms });

      return {
        prefix,
        term: v,
      };

    //case "set":
    default:
      throw "";
  }
}
function dotExpandTerms(t) {
  let prefix = [];
  let terms = [];
  t.forEach((term) => {
    let { prefix: p, term: t } = dotExpandTerm(term);
    prefix = prefix.concat(p);
    terms.push(t);
  });
  return { prefix, terms };
}

function dotExpandRelation(p) {
  let { prefix, terms } = dotExpandTerms(p.terms);
  return { prefix, relation: { ...p, terms } };
}

function dotExpandQuery(q) {
  let prefix = [];
  let relations = [];
  q.forEach((pattern) => {
    let { prefix: p, relation: r } = dotExpandRelation(pattern);
    prefix = prefix.concat(p);
    relations.push(r);
  });
  return { prefix, query: relations };
}
function dotExpandEpisode(expr) {
  let recurse = dotExpandEpisode;
  let mk = (prefix, episode) => ({ prefix, episode });
  switch (expr.tag) {
    case "done": {
      return mk([], expr);
    }
    case "literal": {
      return mk([], expr);
    }
    case "concurrent":
    case "sequence": {
      let { a, b } = expr;
      let ra = recurse(a);
      let rb = recurse(b);
      return mk(ra.prefix.concat(rb.prefix), { ...expr, a: ra.episode, b: rb.episode });
    }
    case "with-tuples": {
      let { tuples, body } = expr;
      // may update binding:
      let { prefix, query } = dotExpandQuery(tuples);
      let r = recurse(body);
      return mk(r.prefix.concat(prefix), { ...expr, tuples: query, body: r.episode });
    }
    default:
      throw "";
  }
}

function dotExpandRuleBody(body) {
  let fix = (prefix) => prefix.map((pattern) => ({ tag: "observation", pattern }));
  return body
    .map((p) => {
      switch (p.tag) {
        case "observation": {
          let { prefix, relation } = dotExpandRelation(p.pattern);
          return fix(prefix).concat([{ tag: "observation", pattern: relation }]);
        }
        // todo retract
        case "retract": {
          let { prefix, query } = dotExpandQuery(p.query);
          return fix(prefix).concat([{ tag: "retract", query: query }]);
        }
        case "assert": {
          let { prefix, query } = dotExpandQuery(p.tuples);
          return fix(prefix).concat([{ tag: "assert", tuples: query }]);
        }
        case "subquery": {
          let { name } = p;
          let { prefix, query } = dotExpandQuery(p.query);
          return [{ tag: "subquery", name, query: prefix.concat(query) }];
        }
        case "choose":
          return [p];
        case "do": {
          let { prefix, episode } = dotExpandEpisode(p.value);
          return fix(prefix).concat([{ tag: "do", value: episode }]);
        }
        case "done":
          return [p];
        case "subbranch":
          return [{ tag: "subbranch", branch: dotExpandRuleBody(p.branch) }];
        case "binOp":
          let r1 = dotExpandTerm(p.l);
          let r2 = dotExpandTerm(p.r);
          return fix(r1.prefix.concat(r2.prefix)).concat([
            { ...p, l: r1.term, r: r2.term },
          ]);
        default:
          throw "";
      }
    })
    .flat(1);
}

function parseProgram(text) {
  function appendDone(body) {
    if (body.length === 0) return [{ tag: "done" }];
    let last = body[body.length - 1];
    if (last.tag !== "done" && last.tag !== "do") return body.concat([{ tag: "done" }]);
    return body;
  }
  function fixBody(body) {
    return dotExpandRuleBody(appendDone(body));
  }
  // filter comments. todo: lexer
  text = text
    .split("\n")
    .filter((l) => !l.match(/^\s*#/))
    .join("\n");
  // parse
  let exprs = parseNonterminal("program", text);
  let defs = new ArrayMap();
  let triggers = new ArrayMap();
  for (let e of exprs) {
    if (e === null) continue;
    let { type, head, body } = e;
    // unfold dot notation
    body = fixBody(body);
    switch (type) {
      case "def": {
        defs.add(head, body);
        break;
      }
      case "trigger": {
        triggers.add(head, body);
        break;
      }
      default:
        throw "";
    }
  }
  return { defs, triggers };
}

function main(rules) {
  let program = {
    rules,
    //db: emptyDb(),
    js: {
      add: (a, b) => mkInt(a.value + b.value),
      sub: (a, b) => mkInt(a.value - b.value),
    },
  };

  let now = mkEpisodeByName(rules, "game");
  now.db = emptyDb();
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
    history.push(cloneEpisode(now));
    //history.push({ now, db: cloneDb(program.db) });
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
    render(tuplesOfDb(now.db), app);
    //render(tuplesOfDb(program.db), app);
    console.log(options.length);
    scrollBody();
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

//window.onload = () => loadRules(main);
window.onload = deriveTests.runTests;

/* todo

! finish local db changes
! integrate SAD

SAD
  ! incremental
  fix non-linear issue
  parsing for declare arity/reduction type
  get rid of `dependencies`
  static check for unbound head variables

js predicates
  int range
  pass in db
  input/output modes
  ? `eval` with types

actor: dom
  choice icons + run blocks

? collapse any bubble
replay
header containing viz instructions

? atomic update

fix highlighted choose menu
fix after turn nesting issue
? `new` operation

early exit queries that can't match
  fix "1 out of n match" visual issue

count
  not, comparisons
actors
  default (single choice, null choice), helper

rule editor
  insert to db while running
  value breakpoints?

*/
