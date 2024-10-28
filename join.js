import { assert } from "./collections.js";
import { Binding } from "./binding.js";

const str = (e) => JSON.stringify(e, null, 2);
const pp = (x) => console.log(str(x));
const af = Array.from;

function scrollBody() {
  window.scrollTo(0, document.body.scrollHeight);
}

// todo: db class
function emptyDb() {
  return new Map();
}

function ppWorld(world) {
  result = "";
  for (let [key, val] of world) {
    result += `<p>${key}: `;
    result += JSON.stringify(val);
    result += "</p>";
  }
  return result;
}

/* variables */
function selectRel(db, tag) {
  let v = db.get(tag);
  if (v === undefined) {
    v = new Map();
    db.set(tag, v);
  }
  return v;
}
function key(tuple) {
  return JSON.stringify(tuple);
}
function getKey(rel, key) {
  let v = rel.get(key);
  return v === undefined ? 0 : v[1];
}
function relAddTupleWithKey(rel, k, tuple, count = 1) {
  let v = getKey(rel, k) + count;
  if (v > 0) rel.set(k, [tuple, v]);
  else rel.delete(k);
}
function relAddTuple(rel, tuple, count = 1) {
  let k = key(tuple);
  return relAddTupleWithKey(rel, k, tuple, count);
}
function dbGet(db, tag, tuple) {
  return getKey(selectRel(db, tag), key(tuple));
}
// mutates left arg
function relAddRel(rel1, rel2) {
  for (let [k, v] of rel2.entries()) {
    relAddTupleWithKey(rel1, k, v[0], v[1]);
  }
}
function dbContains(db, tag, tuple) {
  return dbGet(db, tag, tuple) > 0;
}
function dbAddTuple(db, tag, tuple, count = 1) {
  relAddTuple(selectRel(db, tag), tuple, count);
}
// mutates left arg
function dbAddDb(db1, db2) {
  for (let [tag, rel] of db2.entries()) {
    relAddRel(selectRel(db1, tag), rel);
  }
  return db1;
}
function addDbs(dbs) {
  return dbs.reduce(dbAddDb, emptyDb());
}
function cloneDb(db) {
  return dbAddDb(emptyDb(), db);
}

// todo, delta of this
function dedup(db) {
  for (let rel of db.values()) {
    for (let [key, [tuple, v]] of rel.entries()) {
      if (v > 0) rel.set(key, [tuple, 1]);
      if (v < 0) rel.set(key, [tuple, -1]);
    }
  }
}
function dbOfList(array) {
  let r = emptyDb();
  for (let t of array) {
    dbAddTuple(r, t[0], t[1]);
  }
  return r;
}

function iterRel(db, tag) {
  return selectRel(db, tag).values();
}
function iterRelTuples(db, tag) {
  // todo: use core-utils iterator polyfill
  return Array.from(iterRel(db, tag)).map(([t, _]) => t);
}

function* iterDb(db) {
  for (let key of db.keys()) {
    for (let [tuple, v] of iterRel(db, key)) {
      yield [key, tuple, v];
    }
  }
}
function* tuplesOfDb(db) {
  for (let [key, tuple, _b] of iterDb(db)) {
    yield [key, tuple];
  }
}
function printDb(db) {
  return af(db.entries()).map(([tag, rel]) => [
    tag,
    af(rel.entries()).map(([key, [_, c]]) => [key, c]),
  ]);
}

function isLiteral(term) {
  assert(term.tag !== undefined);
  return term.tag !== "var";
}
function isHole(term) {
  return term.tag === "var" && term.value === "_";
}
function isVar(term) {
  return !isLiteral(term) && !isHole(term);
}

function evalTerm(js, binding, term) {
  if (isLiteral(term)) {
    if (term.tag === "call") {
      let args = term.args.map((v) => evalTerm(js, binding, v));
      return js[term.fn](...args);
    } else {
      assert(term.tag === "int" || term.tag === "sym");
      return term;
    }
  }
  let maybeValue = binding.get(term.value);
  if (maybeValue !== undefined) return maybeValue;
  return term;
}

function emptyBinding() {
  return new Binding();
}

// todo profile
function extendBinding(c, tag, tuple, values, modifiers) {
  for (let index = 0; index < values.length; index++) {
    let term = values[index];
    if (isLiteral(term) && !valEqual(term, tuple[index])) return false;
  }
  c = c.clone();
  for (let index = 0; index < values.length; index++) {
    let term = values[index];
    if (isVar(term)) c.set(term.value, tuple[index]);
  }
  let fact = [tag, tuple];
  modifiers.forEach((mod) => {
    c.notes.add(mod, fact);
  });
  c.notes.add("used", fact);
  return c;
}
function* joinBindings(js, context, { pattern: { tag, terms, modifiers }, tuples }) {
  for (let c of context) {
    let values = terms.map((t) => evalTerm(js, c, t));
    for (let tuple of tuples) {
      let newC = extendBinding(c, tag, tuple, values, modifiers || []);
      if (newC !== false) yield newC;
    }
  }
}

function evalQuery(db, js, query, context = [emptyBinding()]) {
  // redundant. done to ensure result does not contain any input context
  if (query.length === 0) return context.map((c) => c.clone());

  return query
    .map((pattern) => {
      assert(pattern.tag && pattern.terms);
      //assert(Array.isArray(pattern) && pattern.length === 2);
      return { pattern, tuples: iterRelTuples(db, pattern.tag) };
    })
    .reduce((context, b) => joinBindings(js, context, b), context);
}

function valEqual(a, b) {
  if (a.tag !== b.tag) return false;
  assert(a.tag !== "var" && a.tag !== "call");
  switch (a.tag) {
    case "sym":
    case "int":
      return a.value === b.value;
  }
}

// term constructors
function mkInt(value) {
  return { tag: "int", value };
}
function mkVar(value) {
  return { tag: "var", value };
}
function mkSym(value) {
  return { tag: "sym", value };
}
function mkSet(value) {
  return { tag: "set", value };
}

function ppTerm(term) {
  switch (term.tag) {
    case "var":
      return term.value;
    case "sym":
      return `'${term.value}`;
    case "int":
      return `${term.value}`;
    case "set":
      return ppContext(term.value);
    case "call":
      return `#${term.fn}(${term.args.map(ppTerm).join(", ")})`;
    default:
      throw "todo";
  }
}

function ppQuery(ps) {
  return ps.map(({ tag, terms }) => [tag].concat(terms.map(ppTerm)).join(" ")).join(", ");
}
function ppTuples(ps) {
  return ps.map(([tag, terms]) => [tag].concat(terms.map(ppTerm)).join(" ")).join(", ");
}
function ppBinding(binding) {
  let pairs = [];
  for (let key of binding) {
    if (key[0] !== "_") pairs.push(`${key}: ${ppTerm(binding.get(key))}`);
  }
  let deleted = binding.notes.get("delete");
  let added = binding.notes.get("add");
  if (deleted.length + added.length > 0)
    pairs.push(`(${ppTuples(deleted)}) => (${ppTuples(added)})`);
  return `{${pairs.join(", ")}}`;
}
function ppContext(context) {
  return `[${context.map(ppBinding).join("; ")}]`;
}

let globalIdCounter = 0;
function freshId() {
  return { tag: "sym", value: globalIdCounter++ };
}

function substitute(js, binding, terms) {
  return terms.map((term) => {
    if (isLiteral(term)) return evalTerm(js, binding, term);
    if (isHole(term)) {
      return freshId();
    } else {
      assert(isVar(term));
      let v = term.value;
      let maybeV = binding.get(v);
      if (maybeV) return maybeV;
      else {
        let id = freshId();
        binding.set(v, id);
        return id;
      }
    }
  });
}

export {
  af,
  str,
  emptyDb,
  printDb,
  dbOfList,
  dbAddTuple,
  dbAddDb,
  addDbs,
  dbContains,
  isLiteral,
  valEqual,
  evalTerm,
  emptyBinding,
  evalQuery,
  freshId,
  substitute,
  ppQuery,
  ppTerm,
  ppBinding,
  ppContext,
  mkInt,
  mkVar,
  mkSym,
  mkSet,
  tuplesOfDb,
  pp,
  cloneDb,
};
