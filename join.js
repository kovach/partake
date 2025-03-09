import { ArrayMap, assert, ap } from "./collections.js";
//import { Binding } from "./binding.js";

const str = (e) => JSON.stringify(e, null, 2);
const pp = (x) => console.log(str(x));
const af = Array.from;

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
// todo
function key(tuple) {
  return JSON.stringify(tuple);
}

function getKey(rel, key) {
  let v = rel.get(key);
  return v === undefined ? 0 : v[1];
}
function relAddTupleWithKey(rel, k, tuple, count = 1, add) {
  let v = add(getKey(rel, k), count);
  if (v > 0) rel.set(k, [tuple, v]);
  else rel.delete(k);
}
function relAddTuple(rel, tuple, count = 1, add) {
  let k = key(tuple);
  return relAddTupleWithKey(rel, k, tuple, count, add);
}
function dbGet(db, tag, tuple) {
  return getKey(selectRel(db, tag), key(tuple));
}
// mutates left arg
function relAddRel(rel1, rel2, add) {
  for (let [k, v] of rel2.entries()) {
    relAddTupleWithKey(rel1, k, v[0], v[1], add);
  }
}
function dbContains(db, tag, tuple) {
  return dbGet(db, tag, tuple) > 0;
}
function dbAddTuple(db, tag, tuple, count = 1) {
  relAddTuple(selectRel(db, tag), tuple, count, db.add);
}
// mutates left arg
function dbAddDb(db1, db2) {
  for (let [tag, rel] of db2.entries()) {
    relAddRel(selectRel(db1, tag), rel, db1.add);
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
  return af(db.entries())
    .map(([tag, rel]) => [
      tag,
      af(rel.entries())
        .map(([key, [_, c]]) => [key, c])
        .sort(([a, a_], [b, b_]) => a.localeCompare(b)),
    ])
    .sort(([a, a_], [b, b_]) => a.localeCompare(b));
}

function dbEq(db1, db2) {
  return JSON.stringify(printDb(db1)) === JSON.stringify(printDb(db2));
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
    } else if (term.tag === "bind") {
      return term; // todo: handle variables. change representation?
    } else {
      assert(term.tag === "int" || term.tag === "sym");
      return term;
    }
  }
  let maybeValue = binding.get(term.value);
  if (maybeValue !== undefined) return maybeValue;
  return term;
}

function cloneTerm(term) {
  switch (term.tag) {
    case "var":
    case "sym":
    case "int":
      return structuredClone(term);
    case "set":
      return { tag: "set", value: term.value.map((b) => b.clone()) };
    case "box":
      return term; // !
    case "bind":
      return { tag: "bind", value: term.value.clone() };
    default:
      throw "";
  }
}
class Binding {
  substitution = new Map();
  notes = new ArrayMap();

  constructor(values = []) {
    for (let [k, v] of values) this.set(k, v);
  }

  toJSON() {
    return `{${Array.from(this.substitution.entries())
      .map(([k, v]) => k + ": " + ppTerm(v))
      .join(",")}}`;
  }

  *[Symbol.iterator]() {
    for (let k of this.substitution.keys()) yield k;
  }

  clone() {
    let m = new Binding();
    //m.notes = new ArrayMap( new Map(structuredClone(Array.from(this.notes.map.entries()))));
    m.notes = this.notes.clone();
    m.substitution = this.substitution.map(cloneTerm);
    return m;
  }

  // all keys in this appear with the same value in b
  // todo: allow vars in b (unifyLe)?
  le(b) {
    for (let [key, val] of this.substitution.entries()) {
      if (!b.has(key) || !valEqual(b.get(key), val)) return false;
    }
    return true;
  }
  unify(b) {
    let values = [];
    for (let [key, val] of this.substitution.entries()) {
      if (b.has(key)) {
        console.log("both: ", key);
      }
      if (b.has(key) && !valEqual(b.get(key), val)) return false;
      values.push([key, val]);
    }
    for (let [key, val] of b.substitution.entries()) {
      values.push([key, val]);
    }
    console.log("done");
    return new Binding(values);
  }
  set(key, val) {
    this.substitution.set(key, val);
    return this;
  }
  get(key) {
    return this.substitution.get(key);
  }
  has(key) {
    return this.get(key) !== undefined;
  }
  eq(b) {
    for (let [key, val] of this.substitution.entries()) {
      if (!valEqual(b.get(key), val)) return false;
    }
    return true;
  }
}
function emptyBinding() {
  return new Binding();
}

function valEqual(a, b) {
  if (a.tag !== b.tag) return false;
  assert(a.tag !== "var" && a.tag !== "call");
  switch (a.tag) {
    case "sym":
    case "int":
      return a.value === b.value;
    case "box":
      //console.log("box-eq? ", a.value, b.value);
      //console.log(JSON.stringify(a.value), JSON.stringify(b.value));
      return JSON.stringify(a.value) === JSON.stringify(b.value); // TODO
    case "bind":
      return a.value.eq(b.value, valEqual);
    default:
      throw "";
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
function mkBox(value) {
  return { tag: "box", value };
}
function mkBind(value) {
  return { tag: "bind", value };
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
    case "bind":
      return term.value.toJSON();
    case "box":
      let content = JSON.stringify(term.value);
      let cutoff = 50;
      if (content.length > cutoff)
        content =
          content.slice(0, cutoff) + `...${content.length - cutoff} chars omitted`;
      return `[box: ${content}]`;
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
function uniqueInt() {
  return globalIdCounter++;
}
function freshId() {
  return mkSym(uniqueInt());
}

function substituteTerm(js, binding, term) {
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
}

function substitute(js, binding, terms) {
  return terms.map(substituteTerm[ap](js, binding));
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
  isVar,
  isLiteral,
  isHole,
  valEqual,
  evalTerm,
  emptyBinding,
  evalQuery,
  freshId,
  uniqueInt,
  substituteTerm,
  substitute,
  ppQuery,
  ppTerm,
  ppBinding,
  ppContext,
  mkInt,
  mkVar,
  mkSym,
  mkSet,
  mkBox,
  mkBind,
  tuplesOfDb,
  pp,
  cloneDb,
  dbEq,
  extendBinding,
  ppTuples,
  Binding,
};
