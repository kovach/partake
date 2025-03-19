import { ArrayMap, assert, ap } from "./collections.js";

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
function isSym(term) {
  return term.tag === "sym";
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

  clone() {
    let m = new Binding();
    //m.notes = new ArrayMap( new Map(structuredClone(Array.from(this.notes.map.entries()))));
    m.notes = this.notes.clone();
    m.substitution = this.substitution.map(cloneTerm);
    return m;
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
  size() {
    return this.substitution.size;
  }
  *entries() {
    yield* this.substitution.entries();
  }
  *[Symbol.iterator]() {
    yield* this.entries();
  }
  // all keys in this appear with the same value in b
  // todo: allow vars in b (unifyLe)?
  le(b) {
    for (let [key, val] of this.entries()) {
      if (!b.has(key) || !valEqual(b.get(key), val)) return false;
    }
    return true;
  }
  toJSON() {
    return `{${Array.from(this.entries())
      .map(([k, v]) => k + ": " + ppTerm(v))
      .join(",")}}`;
  }
  unify(b) {
    let values = [];
    for (let [key, val] of this.substitution.entries()) {
      if (b.has(key) && !valEqual(b.get(key), val)) return false;
      values.push([key, val]);
    }
    for (let [key, val] of b.substitution.entries()) {
      values.push([key, val]);
    }
    console.log("done");
    return new Binding(values);
  }
  eq(b) {
    for (let [key, val] of this.entries()) {
      if (!valEqual(b.get(key), val)) return false;
    }
    return this.size() === b.size();
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

function ppQuantifier(quantifier) {
  switch (quantifier.tag) {
    case "eq":
      return `${quantifier.count}`;
    case "random":
      return `(random ${quantifier.count})`;
    //case "limit":
    //  return `max ${quantifier.count}`;
    //case "amapLimit":
    //  return `~${quantifier.count}`;
  }
}
function ppQuery(ps) {
  return ps.map(({ tag, terms }) => [tag].concat(terms.map(ppTerm)).join(" ")).join(", ");
}
function ppRuleBody(b) {
  return b.map(ppEpisode);
}
function ppEpisode(e) {
  switch (e.tag) {
    case "observation": {
      return `${ppQuery([e.pattern])}`;
    }
    case "choose": {
      let { quantifier, value } = e;
      if (value.query) {
        return `choose ${ppQuantifier(quantifier)} (${ppQuery(value.query)})`;
      } else {
        assert(value.options);
        return `choose ${ppQuantifier(quantifier)} (${value.options.map((b) =>
          b.toJSON()
        )})`;
      }
    }
    case "do": {
      let {
        value: { name, tuples },
      } = e;
      if (!tuples || tuples.length === 0) return `~${name}`;
      return `~${name} [ ${ppQuery(tuples)} ]`;
    }
    case "assert": {
      let { tuple } = e;
      return `+${ppQuery([tuple])}`;
    }
    case "branch": {
      let i = e.value
        .map(({ id, body: e }) => "( " + id + ": " + ppRuleBody(e) + ")")
        .join(" ");
      return `branch (${i})`;
    }
    case "subStory": {
      return `(${ppRuleBody(e.story)})`;
    }
    case "countIf": {
      return `if (${ppQuery(e.value)})`;
    }
    case "countNot": {
      return `not (${ppQuery(e.value)})`;
    }
    case "deictic": {
      let { id, value } = e;
      return `~${id} := ${ppTerm(value)}`;
    }
    default:
      throw "";
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
    case "set":
      return ppContext(term.value);
    case "call":
      return `#${term.fn}(${term.args.map(ppTerm).join(", ")})`;
    case "bind":
      return term.value.toJSON();
    case "box":
      // todo
      if (
        Array.isArray(term.value) &&
        term.value.some((elem) => elem.tag !== undefined)
      ) {
        return `(box:[${term.value.map(ppEpisode).join(", ")}])`;
      } else {
        let content = JSON.stringify(term.value);
        let cutoff = 50;
        if (content.length > cutoff)
          content =
            content.slice(0, cutoff) + `...${content.length - cutoff} chars omitted`;
        return `(box: ${content})`;
      }
    case "neg":
      return `(- ${ppTerm(term.value)})`;
    case "indexical":
      return `~${term.value}`;
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

// todo: rename/cleanup
function evalTerm(js, location, binding, term) {
  let rec = (t) => evalTerm(js, location, binding, t);
  if (isLiteral(term)) {
    if (term.tag === "call") {
      let args = term.args.map(rec);
      return js[term.fn](...args);
    } else if (term.tag === "bind") {
      return term; // todo: handle variables. change representation?
    } else if (term.tag === "neg") {
      let v = rec(term.value);
      assert(!isVar(v));
      return mkInt(-v.value);
    } else if (term.tag === "indexical") {
      return js._is.get(term.value, location);
    } else {
      assert(term.tag === "int" || term.tag === "sym");
      return term;
    }
  }
  let maybeValue = binding.get(term.value);
  if (maybeValue !== undefined) return maybeValue;
  return term;
}

function evalTermStrict(js, location, binding, term) {
  let x = evalTerm(js, location, binding, term);
  assert(!isVar(x));
  return x;
}

//function substituteTerm(js, location, binding, term) {
//  if (isLiteral(term)) return evalTerm(js, location, binding, term);
//  if (isHole(term)) {
//    return freshId();
//  } else {
//    assert(isVar(term));
//    let v = term.value;
//    let maybeV = binding.get(v);
//    if (maybeV !== undefined) return maybeV;
//    else {
//      let id = freshId();
//      binding.set(v, id);
//      return id;
//    }
//  }
//}
//
//function substitute(js, location, binding, terms) {
//  return terms.map(substituteTerm[ap](js, location, binding));
//}

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
  isSym,
  valEqual,
  evalTerm,
  evalTermStrict,
  emptyBinding,
  evalQuery,
  freshId,
  uniqueInt,
  //substituteTerm,
  //substitute,
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
