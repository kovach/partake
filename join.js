import { assert, ArrayMap } from "./collections.js";
import { Binding } from "./binding.js";

const str = (e) => JSON.stringify(e, null, 2);
const pp = (x) => console.log(str(x));
const compose = (f, g) => (x) => f(g(x));
const af = Array.from;
const afs = (x) => JSON.stringify(Array.from(x));

const rootContainer = "#app";

function scrollBody() {
  window.scrollTo(0, document.body.scrollHeight);
}
function addDoc(x) {
  document.querySelector(rootContainer).innerHTML += `<p>${x}</p>`;
  scrollBody();
}
function clearDoc(x) {
  document.querySelector(rootContainer).innerHTML = "";
  scrollBody();
}

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
function relAddRel(rel1, rel2) {
  // mutates left arg
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
function dbAddDb(db1, db2) {
  // mutates left arg
  for (let [tag, rel] of db2.entries()) {
    relAddRel(selectRel(db1, tag), rel);
  }
  return db1;
}
function addDbs(dbs) {
  return dbs.reduce(dbAddDb, emptyDb());
}
function clone(db) {
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
const emit = dbAddTuple;
const remove = (db, tag, tuple) => dbAddTuple(db, tag, tuple, -1);

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
function printDb(db) {
  return af(db.entries()).map(([tag, rel]) => [
    tag,
    af(rel.entries()).map(([key, [_, c]]) => [key, c]),
  ]);
}
/* end variables */

function isLiteral(term) {
  assert(term.tag !== undefined);
  return term.tag !== "var";
}

function isVar(term) {
  return !isLiteral(term);
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
function* joinBindings(js, cs, { pattern: { tag, terms, modifiers }, tuples }) {
  for (let c of cs) {
    let values = terms.map((t) => evalTerm(js, c, t));
    for (let tuple of tuples) {
      let newC = extendBinding(c, tag, tuple, values, modifiers || []);
      if (newC !== false) yield newC;
    }
  }
}

function evalQuery(db, js, query, context = [emptyBinding()]) {
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

function ppTerm(term) {
  switch (term.tag) {
    case "var":
      return term.value;
    case "sym":
      return `'${term.value}`;
    case "int":
      return `${term.value}`;
    default:
      throw "todo";
  }
}
const ppQuery = (ps) => {
  return ps.map(({ tag, terms }) => [tag].concat(terms.map(ppTerm)).join(" ")).join(", ");
};

let globalIdCounter = 0;
function freshId() {
  return { tag: "sym", value: globalIdCounter++ };
}

function unrename(js, binding, terms) {
  return terms.map((term) => {
    if (isLiteral(term)) return evalTerm(js, binding, term);
    else {
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
  unrename,
  dbOfList,
  dbAddTuple,
  af,
  str,
  clone,
  emptyDb,
  dbContains,
  evalQuery,
  isLiteral,
  valEqual,
  evalTerm,
  freshId,
  emptyBinding,
  ppQuery,
  ppTerm,
};
