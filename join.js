import { assert } from "./collections.js";
const str = JSON.stringify;
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
  console.log(
    af(db.entries())
      .map(([tag, rel]) => [tag, af(rel.entries()).map(([key, [_, c]]) => [key, c])])
      .map((x) => str(x))
  );
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
  if (term.value in binding) return binding[term.value];
  return term;
}

// todo profile
function extendBinding(c, tag, tuple, values) {
  for (let index = 0; index < values.length; index++) {
    let term = values[index];
    if (isLiteral(term) && !valEqual(term, tuple[index])) return false;
  }
  c = structuredClone(c);
  for (let index = 0; index < values.length; index++) {
    let term = values[index];
    if (isVar(term)) c.binding[term.value] = tuple[index];
  }
  c.used.push([tag, tuple]);
  return c;
}
function* joinBindings(js, cs, { tag, tuples, terms }) {
  for (let c of cs) {
    let values = terms.map((t) => evalTerm(js, c.binding, t));
    for (let tuple of tuples) {
      let newC = extendBinding(c, tag, tuple, values);
      if (newC !== false) yield newC;
    }
  }
}

function evalQuery(db, js, query, context = [{ binding: {}, used: [] }]) {
  return query
    .map((pattern) => {
      assert(Array.isArray(pattern) && pattern.length === 2);
      let [tag, terms] = pattern;
      return { tag, terms, tuples: iterRelTuples(db, tag) };
    })
    .reduce((a, b) => joinBindings(js, a, b), context);
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

function joinTuples(t, s) {
  t = structuredClone(t);
  for (let key in s) {
    if (key in t) {
      if (!valEqual(t[key], s[key])) return false;
    } else t[key] = s[key];
  }
  return t;
}

function joinWeightedTuples(t_, s_) {
  let [t, tv] = t_;
  t = structuredClone(t);
  let [s, sv] = s_;
  // in!
  for (let key in s) {
    if (key in t) {
      if (t[key] != s[key]) return false;
    } else t[key] = s[key];
  }
  return [t, tv * sv];
}

// b *must* be re-startable
function* join(a, b) {
  for (let t1 of a) {
    for (let t2 of b) {
      let t = joinWeightedTuples(t1, t2);
      if (t !== false) yield t;
    }
  }
}

// todo: only works on numerically indexed tuples
function rename(tuple, names) {
  let result = {};
  let i = 0;
  for (let name of names) {
    if (name[0] === "`" || name[0] === "'") {
      if (tuple[i] !== name.slice(1)) return false;
    } else {
      if ((name in result && result[name] !== tuple[i]) || !(i in tuple)) return false;
      result[name] = tuple[i];
    }
    i++;
  }
  return result;
}

function* selectPattern(db, p) {
  for (let [tuple, count] of iterRel(db, p[0])) {
    let t = rename(tuple, p[1]);
    if (t !== false) yield [t, count];
  }
}

const joinsWeighted = (db, ps, init = [{}, 1]) =>
  ps.map((p) => selectPattern(db, p)).reduce(join, [init]);

const ppQuery = (ps) => {
  return ps.map(([tag, vs]) => [tag].concat(vs).join(" ")).join(", ");
};

// x := f
function parseFnApp(tokens) {
  if (tokens.length >= 3 && tokens[1] === ":=") {
    return [tokens[0], tokens[2], tokens.slice(3)];
  }
  return false;
}

function parseAtom(tokens) {
  if (tokens.length > 0) {
    return [tokens[0], tokens.slice(1)];
  }
  return false;
}
function parseClause(tokens) {
  return parseFnApp(tokens) || parseAtom(tokens);
}

function parseQuery(str) {
  // 'f a b, g b c'
  if (str.trim() === "") return [];
  return str.split(",").map((w) => {
    // ['f', 'a', 'b']
    let tokens = w
      .trim()
      .split(" ")
      .filter((w) => w.length > 0);
    // ['f', ['a', 'b']]
    return parseClause(tokens);
  });
}

let globalIdCounter = 0;
function freshId() {
  return { tag: "sym", value: globalIdCounter++ };
}

function unrename(js, tuple, terms) {
  return terms.map((term) => {
    if (isLiteral(term)) return evalTerm(js, tuple, term);
    else {
      assert(isVar(term));
      let v = term.value;
      if (v in tuple) return tuple[v];
      else {
        let id = freshId();
        tuple[v] = id;
        return id;
      }
    }
  });
}

function evalRule(db, { query, output }) {
  let bindings = joinsWeighted(db, query);
  for (let tuple of bindings) {
    for (let pattern of output) {
      emit(world, pattern[0], unrename(tuple, pattern[1]));
    }
  }
}

function parseRule(str) {
  let [query, output] = str.split("->").map(parseQuery);
  return { query, output };
}

function specialRelationHandlerUndo(tag, args) {
  let msg = (name, expected) =>
    `special relation '${name}' takes (${expected.join(",")}) but saw: (${args})`;
  if (tag === "create") {
    assert(args.length === 2, msg("create", ["element-type", "id"]));
    // remove
    getId(args[1]).remove();
  } else if (tag === "style") {
    assert(args.length === 3, msg("style", ["id", "css-prop", "value"]));
    //no-op?
  } else if (tag === "parent") {
    assert(args.length === 2, msg("parent", ["id", "id"]));
    //no-op?
  } else if (tag === "inner") {
    assert(args.length === 2, msg("inner", ["id", "content"]));
    //no-op?
  }
}
function specialRelationHandler(tag, args) {
  let msg = (name, expected) =>
    `special relation '${name}' takes (${expected.join(",")}) but saw: (${args})`;
  if (tag === "create") {
    assert(args.length === 2, msg("create", ["element-type", "id"]));
    createElement(args[0], args[1]);
  } else if (tag === "style") {
    assert(args.length === 3, msg("style", ["id", "css-prop", "value"]));
    getId(args[0]).style[args[1]] = args[2];
  } else if (tag === "parent") {
    assert(args.length === 2, msg("parent", ["id", "id"]));
    childParent(getId(args[0]), getId(args[1]));
  } else if (tag === "inner") {
    assert(args.length === 2, msg("inner", ["id", "content"]));
    getId(args[0]).innerHTML = args[1];
  }
}

export {
  unrename,
  dbOfList,
  parseQuery,
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
};
