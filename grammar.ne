@preprocessor module

# whitespace
_ -> null | _ [\s] {% function() {} %}
__ -> [\s] | __ [\s] {% function() {} %}
comma -> _ "," _ {% () => null %}
op -> "(" _ {% () => null %}
cp -> _ ")" {% () => null %}

number -> [0-9]:+ {% d => parseInt(d[0].join("")) %}

# a2-bc'
identifier -> [a-zA-Z_] [a-zA-Z0-9'_-]:*  {% (d) => d[0] + d[1].join("") %}
# _var, Var
var -> identifier {% id %}

predicate -> identifier {% id %}
# todo
predicate -> identifier "/" identifier {% (d) => d[0] + "/" + d[2] %}

# foo(a, b)
arg_list -> null {% (d) => ([]) %}
arg_list -> term (_ "," _ arg_list):?
  {% (d) => {
    let rest = (d[1] !== null) ? d[1][3] : []
    return [d[0]].concat(rest)
  } %}
fn_call -> "@" identifier _ "(" _ arg_list _ ")"
  {% (d) => ({tag :'call', fn: d[1], args: d[5]}) %}

term -> var {% (d) => ({tag: 'var', value: d[0]}) %}
term -> [0-9]:+ {% (d) => ({tag: 'int', value: parseInt(d[0].join(""))}) %}
term -> fn_call {% id %}
term -> "'" identifier {% (d) => ({tag: 'sym', value: d[1]}) %}
term -> term "." identifier {% (d) => ({tag: 'dot', left: d[0], right: d[2]}) %}
term -> "." predicate {% (d) => ({tag: 'dot', left: null, right: d[1]}) %}

# pred2 x y
#relation -> predicate (__ term):* {% (d) => ({tag: d[0], terms: d[1].map(t => t[1])}) %}
relation -> predicate (__ term):*             {% (d) => ({tag: d[0], terms: d[1].map(t => t[1]).concat([{tag: 'int', value: 1}])}) %}
#relation -> predicate (__ term):*             {% (d) => ({tag: d[1], terms: d[1].map(t => t[1]).concat([true])}) %}
relation -> predicate (__ term):* _ "->" _ term {% (d) => ({tag: d[0], terms: d[1].map(t => t[1]).concat([d[5]])}) %}

# p2 x y, p1 z, foo
relation_list -> relation (_ ","):? {% (d) => [d[0]] %}
relation_list -> relation comma relation_list {% (d) => [d[0]].concat(d[2]) %}

pure_query -> null {% () => [] %}
pure_query -> relation_list {% id %}

bin_op -> "<=" {% id %}
bin_op -> ">=" {% id %}
bin_op -> "<" {% id %}
bin_op -> ">" {% id %}
bin_op -> "=" {% id %}

## section: derivations
derivation -> "---" ("-"):* _ relation_list _ "." {% (d) => ({head: d[3], body: []}) %}
derivation -> relation_list _ "---" ("-"):* _ relation_list _ "." {% (d) => ({head: d[5], body: d[0]}) %}
derivation_block -> (_ derivation):* _ {% (d) => d[0].map((r) => r[1]) %}

## section: rules
#
quantifier -> number {% (d) => ({tag: 'eq', count: d[0]}) %}
quantifier -> "~" _ number {% (d) => ({tag: 'amapLimit', count: d[2]}) %}
quantifier -> "max" _ number {% (d) => ({tag: 'limit', count: d[2]}) %}

# todo: associativity
event_expr -> identifier {% (d) => ({ tag: "literal", name: d[0]}) %}
event_expr -> op event_expr _ ";" _ event_expr cp  {% (d) => ({ tag: "concurrent", a: d[1], b: d[5]}) %}
event_expr -> op event_expr _ "->" _ event_expr cp {% (d) => ({ tag: "sequence", a: d[1], b: d[5]}) %}
event_expr -> "[" _ event_expr _ "|" _ pure_query _ "]" {% (d) => ({ tag: "with-tuples", body: d[2], tuples: d[6]}) %}

episode_expr -> relation {% (d) => [{ tag: "observation", pattern: d[0]}] %}
episode_expr -> op pure_query cp _ "=>" _ op pure_query cp
  {% (d) => [{ tag: "modification", before: d[1], after: d[7] }] %}
episode_expr -> "-(" _ pure_query cp
  {% (d) => [{tag: "retract", query: d[2] }] %}
episode_expr -> "+(" _ pure_query cp
  {% (d) => [{tag: "assert", tuples: d[2] }] %}
episode_expr -> term __ "chooses" __ quantifier __ op pure_query cp
  {% (d) => [{ tag: "subquery", query: d[7], name: '?'},
             { tag: "choose", actor: d[0], quantifier: d[4], name: '?' }] %}
episode_expr -> identifier _ ":=" _ "count" _ op pure_query cp
  {% (d) => [{ tag: "subquery", query: d[7], name: d[0] },
             { tag: "count", name: d[0] }] %}
episode_expr -> term _ bin_op _ term
  {% (d) => [{tag: 'binOp', operator: d[2], l: d[0], r: d[4]}] %}
episode_expr -> "!done" {% () => [{tag: "done"}] %}
episode_expr -> "!do" __ event_expr {% (d) => [{tag: "do", value: d[2]}] %}
episode_expr -> op rule_body cp {% (d) => [{tag: "subbranch", branch: d[1] }] %}

episode_list -> episode_expr (_ ","):? {% (d) => d[0] %}
episode_list -> episode_expr comma episode_list {% (d) => d[0].concat(d[2]) %}

rule_body -> episode_list {% id %}
rule_body -> null {% () => [] %}

rule_separator -> _ ":" _ {% () => 'def' %}
rule_separator -> _ "->" _ {% () => 'trigger' %}

rule -> identifier rule_separator rule_body _ "."
  {% (d) => ({head: d[0], type: d[1], body: d[2] }) %}

program -> (_ rule):* {% (d) => d[0].map((r) => r[1]) %}

main -> program _ {% id %}