const str = JSON.stringify;
const pp = (x) => console.log(str(x));
const compose = (f, g) => (x) => f(g(x));
const af = Array.from;
const afs = (x) => JSON.stringify(Array.from(x));

function assert(cond, msg) {
  if (!cond) throw new Error(msg);
}

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

// display test results on page
function test(fn, ...args) {
  let val = fn(...args);
  let result = val;
  if (Array.isArray(result)) {
    result = result.map((r) => `<li>${str(r)}</li>`).join("");
  } else if (result === undefined) {
    result = "✅";
  } else {
    result = str(result);
  }
  addDoc(
    `${fn.name}(${args
      .map((a) => JSON.stringify(a))
      .join(", ")}): <ul>${result}</li>`
  );
  return val;
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

function redraw() {
  document.querySelector(rootContainer).innerHTML += ` ${ppWorld(world)} `;
  scrollBody();
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
      .map(([tag, rel]) => [
        tag,
        af(rel.entries()).map(([key, [_, c]]) => [key, c]),
      ])
      .map((x) => str(x))
  );
}
/* end variables */

function isLiteral(term) {
  assert(term.tag !== undefined);
  return term.tag !== "var";
}

function isVar(term) {
  assert(term.tag !== undefined);
  return term.tag === "var";
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
  throw "var missing from binding";
}

// todo profile
function extendBinding(js, c, tag, tuple, terms) {
  //if (tag === "in") throw "";
  for (let index = 0; index < terms.length; index++) {
    let term = terms[index];
    if (isLiteral(term)) {
      let val = evalTerm(js, binding, term);
      if (!valEqual(val, tuple[index])) return false;
    } else if (
      term.value in c.binding &&
      !valEqual(c.binding[term.value], tuple[index])
    ) {
      return false;
    }
  }
  c = structuredClone(c);
  for (let index = 0; index < terms.length; index++) {
    let term = terms[index];
    if (isLiteral(term)) continue;
    c.binding[term.value] = tuple[index];
  }
  c.used.push([tag, tuple]);
  return c;
}
function* joinBindings(js, cs, { tag, tuples, terms }) {
  for (let c of cs) {
    for (let tuple of tuples) {
      let c_ = extendBinding(js, c, tag, tuple, terms);
      if (c_ !== false) yield c_;
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
      if ((name in result && result[name] !== tuple[i]) || !(i in tuple))
        return false;
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

/* section:parser */
// todo: use parser generator?
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

// eta-expanded so that it has a `.name`
const pp_parse = (x) => ppQuery(parseQuery(x));

let globalIdCounter = 0;
function freshId() {
  return { tag: "sym", value: globalIdCounter++ };
}

function unrename(js, tuple, terms) {
  let result = [];
  terms.forEach((term) => {
    if (isLiteral(term)) result.push(evalTerm(js, tuple, term));
    else {
      assert(isVar(term));
      //console.log("!!!!!!", term, tuple);
      let v = term.value;
      if (v in tuple) result.push(tuple[v]);
      else {
        let id = freshId();
        tuple[v] = id;
        result.push(id);
      }
    }
  });
  return result;
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
    `special relation '${name}' takes (${expected.join(
      ","
    )}) but saw: (${args})`;
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
    `special relation '${name}' takes (${expected.join(
      ","
    )}) but saw: (${args})`;
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

function collect(i, acc) {
  for (let v of i) acc.push(v);
}

// delta query without specialization
function* delta(ps, x, a) {
  if (ps.length === 0) return [];
  let R = ps[0];
  let S = ps.slice(1);
  let Rx = selectPattern(x, R);
  let Ra = af(selectPattern(a, R));
  let Sx = af(joinsWeighted(x, S));
  let Sa = af(delta(S, x, a));
  for (let t of join(Ra, Sx)) yield t;
  for (let t of join(Rx, Sa)) yield t;
  for (let t of join(Ra, Sa)) yield t;
}

const deltaCollect = (ps, x, a) => af(delta(ps, x, a));
const pq = parseQuery;

// something to note later: https://groups.google.com/g/v8-users/c/jlISWv1nXWU/m/LOLtbuovAgAJ

function evalDelta(db, ddb, { query, output }) {
  //console.log("eval");
  //printDb(ddb);
  let bindings = delta(query, db, ddb);
  bindings = bindings;
  //console.log(afs(bindings));
  let result = emptyDb();
  for (let [tuple, weight] of bindings) {
    for (let pattern of output) {
      let tag = pattern[0];
      let args = unrename(tuple, pattern[1]);
      emit(result, tag, args, weight);
    }
  }
  //printDb(result);
  return result;
}

function doSpecialOutputs(db, result) {
  for (let [tag, tuple, v] of iterDb(result)) {
    if (v > 0) {
      //assert(v === 1, "delta contains > 1 copies of tuple");
      if (dbGet(db, tag, tuple) === 0) specialRelationHandler(tag, tuple);
    }
    if (v < 0) {
      //console.log("removing!");
      //assert(v === -1, "delta contains < -1 copies of tuple");
      if (dbGet(db, tag, tuple) === 1) specialRelationHandlerUndo(tag, tuple);
    }
  }
}

function evalDelta_(db, ddb, rule) {
  let result = evalDelta(db, ddb, rule);
  dbAddDb(db, ddb);
  dbAddDb(db, result);
}

const prog1Text = `
->
  item 'apple 'fruit,
  item 'banana 'fruit,
  item 'spinach 'vegetable,

  in-stock 'apple 'true,
  in-stock 'spinach 'true,
  in-stock 'banana 'false,

  box-unchecked.

item i cat, in-stock i 'true                 -> visible i.
item i cat, in-stock i 'false, box-unchecked -> visible i.

visible i             -> create 'div i,   inner i i.
visible i, item i cat -> create 'div cat, inner cat cat, parent i cat, parent cat 'app.
`;

function parseProgram(text) {
  let rules = text
    .split(".")
    .filter((line) => line.trim().length > 0)
    .map((line) => {
      let rule = parseRule(line);
      return rule;
    });
  let initiate = rules.filter(({ query }) => query.length === 0);
  initiate = initiate.map(({ output }) => output);
  rules = rules.filter(({ query }) => query.length !== 0);
  return { initiate, rules };
}
function initProgram(db, { initiate }) {
  for (let output of initiate) {
    for (let [tag, atoms] of output) {
      emit(db, tag, unrename({}, atoms));
    }
  }
}

const prog1 = parseProgram(prog1Text);

//pp(prog1);
function updateProg(db, ddb, prog) {
  let gas = 10;
  while (ddb.size > 0 && gas-- > 0) {
    //printDb(ddb);
    let delta = emptyDb();
    for (let rule of prog.rules) {
      let d = evalDelta(db, ddb, rule);
      dbAddDb(delta, d);
      //printDb(d);
    }

    doSpecialOutputs(db, ddb);
    dbAddDb(db, ddb);
    //printDb(db);

    //dedup(delta);
    ddb = delta;
  }
  scrollBody();
}

{
  const db = emptyDb();

  function do1() {
    ddb = emptyDb();
    initProgram(ddb, prog1);

    updateProg(db, ddb, prog1);
    printDb(db);
  }

  function do2() {
    ddb = emptyDb();
    emit(ddb, "box-unchecked", [], -1);
    updateProg(db, ddb, prog1);
    printDb(db);
  }

  function do3() {
    ddb = emptyDb();
    emit(ddb, "box-unchecked", [], 1);
    updateProg(db, ddb, prog1);
    printDb(db);
  }

  //do1();
  //do2();
}

const node = {
  db: emptyDb(),
  onChange: (delta) => {},
};

{
  const db = emptyDb();
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
  extendBinding,
};
