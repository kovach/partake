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
fnCall -> "#" identifier _ "(" _ argList _ ")"
  {% (d) => ({tag :'call', fn: d[1], args: d[5]}) %}

term -> var {% (d) => ({tag: 'var', value: d[0]}) %}
term -> [0-9]:+ {% (d) => ({tag: 'int', value: parseInt(d[0].join(""))}) %}
term -> fnCall {% id %}
term -> "'" identifier {% (d) => ({tag: 'sym', value: d[1]}) %}

# pred2 x y -> ["pred", ["x", "y"]]
relation -> predicate (__ term):* {% (d) => {return {tag: d[0], terms: d[1].map(t => t[1])}} %}

# p2 x y, p1 z, foo
relationList -> relation (_ ","):? {% (d) => [d[0]] %}
relationList -> relation comma relationList {% (d) => [d[0]].concat(d[2]) %}

pureQuery -> null {% () => [] %}
pureQuery -> relationList {% id %}

#event_expr -> "." {% (d) => ({ tag: "done"}) %} # todo remove
event_expr -> identifier {% (d) => ({ tag: "literal", name: d[0]}) %}
#event_expr -> "(" _ event_expr _ ")" {% (d) => d[2] %}
event_expr -> op event_expr _ ";" _ event_expr cp  {% (d) => ({ tag: "concurrent", a: d[1], b: d[5]}) %}
event_expr -> op event_expr _ "->" _ event_expr cp {% (d) => ({ tag: "sequence", a: d[1], b: d[5]}) %}
event_expr -> "[" _ event_expr _ "|" _ pureQuery _ "]" {% (d) => ({ tag: "with-tuples", body: d[2], tuples: d[6]}) %}

rule_body -> episode_list {% id %}
rule_body -> null {% () => [] %}

episode_list -> episode_expr (_ ","):? {% (d) => d[0] %}
episode_list -> episode_expr comma episode_list {% (d) => d[0].concat(d[2]) %}

episode_expr -> "!done" {% () => [{tag: "done"}] %}
episode_expr -> "!do" __ event_expr {% (d) => [{tag: "do", value: d[2]}] %}
episode_expr -> relation {% (d) => [{ tag: "observation", pattern: d[0]}] %}
# todo: X> and >X.
episode_expr -> op pureQuery cp _ "=>" _ op pureQuery cp
  {% (d) => [{ tag: "modification", before: d[1], after: d[7]}] %}
episode_expr -> term __ "chooses" __ quantifier __ op pureQuery cp
  {% (d) =>
    [{ tag: "subquery", query: d[7], name: '?'},
     { tag: "choose", actor: d[0], quantifier: d[4], name: '?'}]
  %}
episode_expr -> identifier _ ":=" _ "count" _ op pureQuery cp
  {% (d) =>
    [{ tag: "subquery", query: d[7], name: d[0] },
     { tag: "count", name: d[0] }]
  %}
episode_expr -> term _ binOp _ term
  {% (d) => [{tag: 'binOp', operator: d[2], l: d[0], r: d[4]}] %}

binOp -> "<=" {% id %}
binOp -> ">=" {% id %}
binOp -> "<" {% id %}
binOp -> ">" {% id %}
binOp -> "=" {% id %}

quantifier -> number {% (d) => ({tag: 'eq', count: d[0]}) %}
quantifier -> "~" _ number {% (d) => ({tag: 'amapLimit', count: d[2]}) %}
quantifier -> "max" _ number {% (d) => ({tag: 'limit', count: d[2]}) %}

rule_separator -> _ ":" _ {% () => 'def' %}
rule_separator -> _ "->" _ {% () => 'trigger' %}

rule -> identifier rule_separator rule_body _ "."
  {% (d) => ({head: d[0], type: d[1], body: d[2] }) %}

program -> (_ rule):* _ {% (d) => d[0].map((r) => r[1]) %}

main -> program {% id %}