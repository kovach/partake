// Generated automatically by nearley, version 2.20.1
// http://github.com/Hardmath123/nearley
function id(x) { return x[0]; }
let Lexer = undefined;
let ParserRules = [
    {"name": "_", "symbols": []},
    {"name": "_", "symbols": ["_", /[\s]/], "postprocess": function() {}},
    {"name": "__", "symbols": [/[\s]/]},
    {"name": "__", "symbols": ["__", /[\s]/], "postprocess": function() {}},
    {"name": "comma", "symbols": ["_", {"literal":","}, "_"], "postprocess": () => null},
    {"name": "op", "symbols": [{"literal":"("}, "_"], "postprocess": () => null},
    {"name": "cp", "symbols": ["_", {"literal":")"}], "postprocess": () => null},
    {"name": "number$ebnf$1", "symbols": [/[0-9]/]},
    {"name": "number$ebnf$1", "symbols": ["number$ebnf$1", /[0-9]/], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "number", "symbols": ["number$ebnf$1"], "postprocess": d => parseInt(d[0].join(""))},
    {"name": "identifier$ebnf$1", "symbols": []},
    {"name": "identifier$ebnf$1", "symbols": ["identifier$ebnf$1", /[a-zA-Z0-9'_-]/], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "identifier", "symbols": [/[a-zA-Z_]/, "identifier$ebnf$1"], "postprocess": (d) => d[0] + d[1].join("")},
    {"name": "var", "symbols": ["identifier"], "postprocess": id},
    {"name": "predicate", "symbols": ["identifier"], "postprocess": id},
    {"name": "predicate", "symbols": ["identifier", {"literal":"/"}, "identifier"], "postprocess": (d) => d[0] + "/" + d[2]},
    {"name": "arg_list", "symbols": [], "postprocess": (d) => ([])},
    {"name": "arg_list$ebnf$1$subexpression$1", "symbols": ["_", {"literal":","}, "_", "arg_list"]},
    {"name": "arg_list$ebnf$1", "symbols": ["arg_list$ebnf$1$subexpression$1"], "postprocess": id},
    {"name": "arg_list$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "arg_list", "symbols": ["term", "arg_list$ebnf$1"], "postprocess":  (d) => {
          let rest = (d[1] !== null) ? d[1][3] : []
          return [d[0]].concat(rest)
        } },
    {"name": "fn_call", "symbols": [{"literal":"@"}, "identifier", "_", {"literal":"("}, "_", "arg_list", "_", {"literal":")"}], "postprocess": (d) => ({tag :'call', fn: d[1], args: d[5]})},
    {"name": "term", "symbols": ["var"], "postprocess": (d) => ({tag: 'var', value: d[0]})},
    {"name": "term$ebnf$1", "symbols": [/[0-9]/]},
    {"name": "term$ebnf$1", "symbols": ["term$ebnf$1", /[0-9]/], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "term", "symbols": ["term$ebnf$1"], "postprocess": (d) => ({tag: 'int', value: parseInt(d[0].join(""))})},
    {"name": "term", "symbols": ["fn_call"], "postprocess": id},
    {"name": "term", "symbols": [{"literal":"'"}, "identifier"], "postprocess": (d) => ({tag: 'sym', value: d[1]})},
    {"name": "term", "symbols": ["term", {"literal":"."}, "identifier"], "postprocess": (d) => ({tag: 'dot', left: d[0], right: d[2]})},
    {"name": "term", "symbols": [{"literal":"."}, "predicate"], "postprocess": (d) => ({tag: 'dot', left: null, right: d[1]})},
    {"name": "relation$ebnf$1", "symbols": []},
    {"name": "relation$ebnf$1$subexpression$1", "symbols": ["__", "term"]},
    {"name": "relation$ebnf$1", "symbols": ["relation$ebnf$1", "relation$ebnf$1$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "relation", "symbols": ["predicate", "relation$ebnf$1"], "postprocess": (d) => ({tag: d[0], terms: d[1].map(t => t[1]).concat([{tag: 'int', value: 1}])})},
    {"name": "relation$ebnf$2", "symbols": []},
    {"name": "relation$ebnf$2$subexpression$1", "symbols": ["__", "term"]},
    {"name": "relation$ebnf$2", "symbols": ["relation$ebnf$2", "relation$ebnf$2$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "relation$string$1", "symbols": [{"literal":"-"}, {"literal":">"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "relation", "symbols": ["predicate", "relation$ebnf$2", "_", "relation$string$1", "_", "term"], "postprocess": (d) => ({tag: d[0], terms: d[1].map(t => t[1]).concat([d[5]])})},
    {"name": "relation_list$ebnf$1$subexpression$1", "symbols": ["_", {"literal":","}]},
    {"name": "relation_list$ebnf$1", "symbols": ["relation_list$ebnf$1$subexpression$1"], "postprocess": id},
    {"name": "relation_list$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "relation_list", "symbols": ["relation", "relation_list$ebnf$1"], "postprocess": (d) => [d[0]]},
    {"name": "relation_list", "symbols": ["relation", "comma", "relation_list"], "postprocess": (d) => [d[0]].concat(d[2])},
    {"name": "pure_query", "symbols": [], "postprocess": () => []},
    {"name": "pure_query", "symbols": ["relation_list"], "postprocess": id},
    {"name": "bin_op$string$1", "symbols": [{"literal":"<"}, {"literal":"="}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "bin_op", "symbols": ["bin_op$string$1"], "postprocess": id},
    {"name": "bin_op$string$2", "symbols": [{"literal":">"}, {"literal":"="}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "bin_op", "symbols": ["bin_op$string$2"], "postprocess": id},
    {"name": "bin_op", "symbols": [{"literal":"<"}], "postprocess": id},
    {"name": "bin_op", "symbols": [{"literal":">"}], "postprocess": id},
    {"name": "bin_op", "symbols": [{"literal":"="}], "postprocess": id},
    {"name": "derivation$string$1", "symbols": [{"literal":"-"}, {"literal":"-"}, {"literal":"-"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "derivation$ebnf$1", "symbols": []},
    {"name": "derivation$ebnf$1$subexpression$1", "symbols": [{"literal":"-"}]},
    {"name": "derivation$ebnf$1", "symbols": ["derivation$ebnf$1", "derivation$ebnf$1$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "derivation", "symbols": ["derivation$string$1", "derivation$ebnf$1", "_", "relation_list", "_", {"literal":"."}], "postprocess": (d) => ({head: d[3], body: []})},
    {"name": "derivation$string$2", "symbols": [{"literal":"-"}, {"literal":"-"}, {"literal":"-"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "derivation$ebnf$2", "symbols": []},
    {"name": "derivation$ebnf$2$subexpression$1", "symbols": [{"literal":"-"}]},
    {"name": "derivation$ebnf$2", "symbols": ["derivation$ebnf$2", "derivation$ebnf$2$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "derivation", "symbols": ["relation_list", "_", "derivation$string$2", "derivation$ebnf$2", "_", "relation_list", "_", {"literal":"."}], "postprocess": (d) => ({head: d[5], body: d[0]})},
    {"name": "derivation_block$ebnf$1", "symbols": []},
    {"name": "derivation_block$ebnf$1$subexpression$1", "symbols": ["_", "derivation"]},
    {"name": "derivation_block$ebnf$1", "symbols": ["derivation_block$ebnf$1", "derivation_block$ebnf$1$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "derivation_block", "symbols": ["derivation_block$ebnf$1", "_"], "postprocess": (d) => d[0].map((r) => r[1])},
    {"name": "quantifier", "symbols": ["number"], "postprocess": (d) => ({tag: 'eq', count: d[0]})},
    {"name": "quantifier", "symbols": [{"literal":"~"}, "_", "number"], "postprocess": (d) => ({tag: 'amapLimit', count: d[2]})},
    {"name": "quantifier$string$1", "symbols": [{"literal":"m"}, {"literal":"a"}, {"literal":"x"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "quantifier", "symbols": ["quantifier$string$1", "_", "number"], "postprocess": (d) => ({tag: 'limit', count: d[2]})},
    {"name": "event_expr", "symbols": ["identifier"], "postprocess": (d) => ({ tag: "literal", name: d[0]})},
    {"name": "event_expr", "symbols": ["op", "event_expr", "_", {"literal":";"}, "_", "event_expr", "cp"], "postprocess": (d) => ({ tag: "concurrent", a: d[1], b: d[5]})},
    {"name": "event_expr$string$1", "symbols": [{"literal":"-"}, {"literal":">"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "event_expr", "symbols": ["op", "event_expr", "_", "event_expr$string$1", "_", "event_expr", "cp"], "postprocess": (d) => ({ tag: "sequence", a: d[1], b: d[5]})},
    {"name": "event_expr", "symbols": [{"literal":"["}, "_", "event_expr", "_", {"literal":"|"}, "_", "pure_query", "_", {"literal":"]"}], "postprocess": (d) => ({ tag: "with-tuples", body: d[2], tuples: d[6]})},
    {"name": "episode_expr", "symbols": ["relation"], "postprocess": (d) => [{ tag: "observation", pattern: d[0]}]},
    {"name": "episode_expr$string$1", "symbols": [{"literal":"="}, {"literal":">"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "episode_expr", "symbols": ["op", "pure_query", "cp", "_", "episode_expr$string$1", "_", "op", "pure_query", "cp"], "postprocess": (d) => [{ tag: "modification", before: d[1], after: d[7] }]},
    {"name": "episode_expr$string$2", "symbols": [{"literal":"-"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "episode_expr", "symbols": ["episode_expr$string$2", "_", "pure_query", "cp"], "postprocess": (d) => [{tag: "retract", query: d[2] }]},
    {"name": "episode_expr$string$3", "symbols": [{"literal":"+"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "episode_expr", "symbols": ["episode_expr$string$3", "_", "pure_query", "cp"], "postprocess": (d) => [{tag: "assert", tuples: d[2] }]},
    {"name": "episode_expr$string$4", "symbols": [{"literal":"c"}, {"literal":"h"}, {"literal":"o"}, {"literal":"o"}, {"literal":"s"}, {"literal":"e"}, {"literal":"s"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "episode_expr", "symbols": ["term", "__", "episode_expr$string$4", "__", "quantifier", "__", "op", "pure_query", "cp"], "postprocess":  (d) => [{ tag: "subquery", query: d[7], name: '?'},
        { tag: "choose", actor: d[0], quantifier: d[4], name: '?' }] },
    {"name": "episode_expr$string$5", "symbols": [{"literal":":"}, {"literal":"="}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "episode_expr$string$6", "symbols": [{"literal":"c"}, {"literal":"o"}, {"literal":"u"}, {"literal":"n"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "episode_expr", "symbols": ["identifier", "_", "episode_expr$string$5", "_", "episode_expr$string$6", "_", "op", "pure_query", "cp"], "postprocess":  (d) => [{ tag: "subquery", query: d[7], name: d[0] },
        { tag: "count", name: d[0] }] },
    {"name": "episode_expr", "symbols": ["term", "_", "bin_op", "_", "term"], "postprocess": (d) => [{tag: 'binOp', operator: d[2], l: d[0], r: d[4]}]},
    {"name": "episode_expr$string$7", "symbols": [{"literal":"!"}, {"literal":"d"}, {"literal":"o"}, {"literal":"n"}, {"literal":"e"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "episode_expr", "symbols": ["episode_expr$string$7"], "postprocess": () => [{tag: "done"}]},
    {"name": "episode_expr$string$8", "symbols": [{"literal":"!"}, {"literal":"d"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "episode_expr", "symbols": ["episode_expr$string$8", "__", "event_expr"], "postprocess": (d) => [{tag: "do", value: d[2]}]},
    {"name": "episode_expr", "symbols": ["op", "rule_body", "cp"], "postprocess": (d) => [{tag: "subbranch", branch: d[1] }]},
    {"name": "episode_list$ebnf$1$subexpression$1", "symbols": ["_", {"literal":","}]},
    {"name": "episode_list$ebnf$1", "symbols": ["episode_list$ebnf$1$subexpression$1"], "postprocess": id},
    {"name": "episode_list$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "episode_list", "symbols": ["episode_expr", "episode_list$ebnf$1"], "postprocess": (d) => d[0]},
    {"name": "episode_list", "symbols": ["episode_expr", "comma", "episode_list"], "postprocess": (d) => d[0].concat(d[2])},
    {"name": "rule_body", "symbols": ["episode_list"], "postprocess": id},
    {"name": "rule_body", "symbols": [], "postprocess": () => []},
    {"name": "rule_separator", "symbols": ["_", {"literal":":"}, "_"], "postprocess": () => 'def'},
    {"name": "rule_separator$string$1", "symbols": [{"literal":"-"}, {"literal":">"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "rule_separator", "symbols": ["_", "rule_separator$string$1", "_"], "postprocess": () => 'trigger'},
    {"name": "rule", "symbols": ["identifier", "rule_separator", "rule_body", "_", {"literal":"."}], "postprocess": (d) => ({head: d[0], type: d[1], body: d[2] })},
    {"name": "program$ebnf$1", "symbols": []},
    {"name": "program$ebnf$1$subexpression$1", "symbols": ["_", "rule"]},
    {"name": "program$ebnf$1", "symbols": ["program$ebnf$1", "program$ebnf$1$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "program", "symbols": ["program$ebnf$1"], "postprocess": (d) => d[0].map((r) => r[1])},
    {"name": "main", "symbols": ["program", "_"], "postprocess": id}
];
let ParserStart = "_";
export default { Lexer, ParserRules, ParserStart };