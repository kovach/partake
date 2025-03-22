import grammar from "./grammar.js";
import { ArrayMap, assert, unzip, zip } from "./collections.js";
import { Binding, mkBind, mkInt, mkVar, uniqueInt } from "./join.js";
import { convertToNewOp } from "./episode.js";

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

// todo: rename
function dotExpandTerm(t) {
  switch (t.tag) {
    case "preBind": {
      let [ks, vs] = unzip(t.value);
      let { prefix, terms } = dotExpandTerms(vs);
      return { prefix, term: mkBind(new Binding(zip(ks, terms))) };
    }
    case "var":
    case "sym":
    case "int":
    case "indexical":
      return { prefix: [], term: t };
    case "neg": {
      let { prefix, term } = dotExpandTerm(t.value);
      return { prefix, term: { ...t, value: term } };
    }
    case "call": {
      let { prefix, terms } = dotExpandTerms(t.args);
      return { prefix, term: { tag: "call", fn: t.fn, args: terms } };
    }
    case "dot": {
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
      terms.push(v, mkInt(1));
      prefix.push({ tag: right, terms });

      return {
        prefix,
        term: v,
      };

      //case "set":
    }
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
    case "literal": {
      return mk([], { ...expr, tuples: [] });
    }
    case "with-tuples": {
      let { tuples, name } = expr;
      // todo cleanup
      let pr = [];
      let bs = [];
      for (let { id, value } of tuples) {
        let { prefix, term } = dotExpandTerm(value);
        pr = pr.concat(prefix);
        bs.push({ id, term });
      }
      return mk(pr, { ...expr, tuples: bs });
      // may update binding:
      //let { prefix, query } = dotExpandQuery(tuples);
      //return mk(prefix, { ...expr, tuples: query, name });
      //let r = recurse(body);
      //return mk(r.prefix.concat(prefix), { ...expr, tuples: query, body: r.episode });
    }
    //case "done": {
    //  return mk([], expr);
    //}
    //case "concurrent":
    //case "sequence": {
    //  let { a, b } = expr;
    //  let ra = recurse(a);
    //  let rb = recurse(b);
    //  return mk(ra.prefix.concat(rb.prefix), { ...expr, a: ra.episode, b: rb.episode });
    //}
    default:
      throw "";
  }
}

function dotExpandRuleBody(body) {
  return body.map(dotExpandOperation).flat(1);

  function fix(prefix) {
    return prefix.map((pattern) => ({ tag: "observation", pattern }));
  }

  function dotExpandOperation(p) {
    switch (p.tag) {
      case "observation": {
        let { prefix, relation } = dotExpandRelation(p.pattern);
        return fix(prefix).concat([{ tag: "observation", pattern: relation }]);
      }
      case "assert": {
        let { prefix, relation } = dotExpandRelation(p.tuple);
        return fix(prefix).concat([{ tag: "assert", tuple: relation }]);
      }
      case "choose":
        let {
          value: { query: q },
        } = p;
        let { prefix, query } = dotExpandQuery(q);
        return [{ ...p, value: { query: [...prefix, ...query] } }];
      case "do": {
        let { prefix, episode } = dotExpandEpisode(p.value);
        return fix(prefix).concat([{ tag: "do", value: episode }]);
      }
      case "branch":
        return {
          ...p,
          value: p.value.map(({ id, body }) => ({ id, body: dotExpandRuleBody(body) })),
        };
      case "subStory":
        return [{ tag: "subStory", story: dotExpandRuleBody(p.story) }];
      case "countIf":
      case "countNot": {
        let { prefix, query } = dotExpandQuery(p.value);
        return [{ ...p, value: [...prefix, ...query] }];
      }
      case "deictic": {
        let { prefix, term } = dotExpandTerm(p.value);
        return [...fix(prefix), { ...p, value: term }];
      }
      //case "binRel": {
      //  let mapping = {
      //    "=": "@eq",
      //    "<": "@lt",
      //    "<=": "@le",
      //    ">": "@gt",
      //    ">=": "@ge",
      //  };
      //  let tag = mapping[p.op];
      //  assert(tag, "invalid operator");
      //  return dotExpandOperation({
      //    tag: "observation",
      //    pattern: { tag, terms: [p.left, p.right, mkInt(1)] },
      //  });
      //}
      //case "retract": {
      //  let { prefix, query } = dotExpandQuery(p.query);
      //  return fix(prefix).concat([{ tag: "retract", query: query }]);
      //}
      //case "subquery": {
      //  let { name } = p;
      //  let { prefix, query } = dotExpandQuery(p.query);
      //  return [{ tag: "subquery", name, query: prefix.concat(query) }];
      //}
      //case "done":
      //  return [p];
      default:
        throw "";
    }
  }
}
function parseProgram(text) {
  text = fixLines(text.split("\n")).join("\n");
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

  function appendDone(body) {
    if (body.length === 0) return [{ tag: "done" }];
    //let last = body[body.length - 1];
    //if (last.tag !== "done" && last.tag !== "do") return body.concat([{ tag: "done" }]);
    return body;
  }
  function fixBody(body) {
    return convertToNewOp(dotExpandRuleBody(appendDone(body)));
  }
  // filter comments. todo: lexer
  function fixLines(lines) {
    let removeCommentFromLine = (s) => /[^#]*/.exec(s)[0];
    lines = lines.map(removeCommentFromLine);
    lines = takeWhile(lines, (line) => line !== "exit.");
    return lines;
  }
}

function takeWhile(arr, p) {
  let result = [];
  for (let i = 0; i < arr.length; i++) {
    if (p(arr[i])) result.push(arr[i]);
    else break;
  }
  return result;
}

export { dotExpandQuery, parseNonterminal, parseProgram };
