import grammar from "./grammar.js";
import { ArrayMap, assert } from "./collections.js";

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
  let removeCommentFromLine = (s) => /[^#]*/.exec(s);
  text = text.split("\n").map(removeCommentFromLine).join("\n");
  let exprs = parseNonterminal("program", text);
  let program = {
    before: new ArrayMap(),
    during: new ArrayMap(),
    after: new ArrayMap(),
  };
  for (let e of exprs) {
    if (e === null) continue;
    let {
      header: {
        id,
        trigger: { type, predicate },
      },
      body,
    } = e;
    body = fixBody(body);
    assert(type);
    program[type].add(predicate, { id, body });
  }
  return program;
}

export { parseNonterminal, parseProgram };
