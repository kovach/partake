@preprocessor module

# whitespace
_ -> null | _ [\s] {% function() {} %}
__ -> [\s] | __ [\s] {% function() {} %}
comma -> _ "," _ {% () => null %}
op -> "(" _ {% () => null %}
cp -> _ ")" {% () => null %}

number -> [0-9]:+ {% d => parseInt(d[0].join("")) %}

# var, Var
identifier -> [a-zA-Z_] [a-zA-Z0-9'_-]:*  {% (d) => d[0] + d[1].join("") %}
var -> identifier {% id %}

# a2bc'
predicate -> identifier {% id %} # [a-z] [a-zA-Z0-9']:* {% (d) => d[0] + d[1].join("") %}

# foo(a, b)
argList -> null {% (d) => ([]) %}
argList -> term (_ "," _ argList):?
  {% (d) => {
    let rest = (d[1] !== null) ? d[1][3] : []
    return [d[0]].concat(rest)
  } %}
fnCall -> "!" identifier _ "(" _ argList _ ")"
  {% (d) => ({tag :'call', fn: d[1], args: d[5]}) %}

term -> var {% (d) => ({tag: 'var', value: d[0]}) %}
term -> [0-9]:+ {% (d) => ({tag: 'int', value: parseInt(d[0].join(""))}) %}
term -> fnCall {% id %}

# pred2 x y -> ["pred", ["x", "y"]]
relation -> predicate (__ term):* {% (d) => {return {tag: d[0], terms: d[1].map(t => t[1])}} %}

# p2 x y, p1 z, foo
pureQuery -> null {% () => [] %}
pureQuery -> relation {% (d) => [d[0]] %}
pureQuery -> relation _ "," _ pureQuery {% (d) => [d[0]].concat(d[4]) %}

event_expr -> "." {% (d) => ({ tag: "done"}) %} # todo remove
event_expr -> identifier {% (d) => ({ tag: "literal", name: d[0]}) %}
event_expr -> "(" _ event_expr _ ")" {% (d) => d[2] %}
event_expr -> event_expr comma event_expr  {% (d) => ({ tag: "concurrent", a: d[0], b: d[2]}) %}
event_expr -> event_expr _ "->" _ event_expr  {% (d) => ({ tag: "sequence", a: d[0], b: d[4]}) %}
event_expr -> "[" _ event_expr _ "|" _ pureQuery _ "]" {% (d) => ({ tag: "with-tuples", body: d[2], tuples: d[6]}) %}

episode_expr -> "done" {% (d) => ({tag: "done"}) %}
episode_expr -> "do" __ event_expr {% (d) => ({tag: "do", value: d[2]}) %}
episode_expr -> relation comma episode_expr {% (d) => ({ tag: "observation", pattern: d[0], rest: d[2] }) %}
# todo: X> and >X.
episode_expr -> op pureQuery cp _ "!" _ op pureQuery cp comma episode_expr
  {% (d) => ({ tag: "modification", before: d[1], after: d[7], rest: d[10] }) %}
episode_expr -> var __ "chooses" __ quantifier __ "?(" _ pureQuery cp comma episode_expr
  {% (d) => ({
      // todo: use unreachable name
      tag: "subquery", query: d[8], name: '_choices', rest:
    { tag: "choose", actor: d[0], quantifier: d[4], name: '_choices', rest: d[11] }})
  %}
episode_expr -> identifier _ ":=" _ "count" _ "(" _ pureQuery cp comma episode_expr
  {% (d) => ({
      tag: "subquery", query: d[8], name: d[0], rest:
    { tag: "count", name: d[0], rest: d[11] }})
  %}
episode_expr -> term _ binOp _ term comma episode_expr
  {% (d) => ({tag: 'binOp', operator: d[2], l: d[0], r: d[4], rest: d[6]}) %}

binOp -> "<=" {% id %}
binOp -> ">=" {% id %}
binOp -> "<" {% id %}
binOp -> ">" {% id %}
binOp -> "=" {% id %}

quantifier -> number {% id %}

rule_separator -> _ ":" _ {% () => 'def' %}
rule_separator -> _ "->" _ {% () => 'trigger' %}
rule -> identifier rule_separator episode_expr _ "."
  {% (d) => ({head: d[0], type: d[1], body: d[2] }) %}

program -> (_ rule):* _ {% (d) => d[0].map((r) => r[1]) %}

main -> program {% id %}