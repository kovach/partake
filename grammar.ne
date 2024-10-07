@preprocessor module

main -> line {% id %}

# var, Var
identifier -> [a-zA-Z_] [a-zA-Z0-9'_-]:*  {% (d) => d[0] + d[1].join("") %}
var -> identifier {% id %}
# a2bc'
predicate -> [a-z] [a-zA-Z0-9']:* {% (d) => d[0] + d[1].join("") %}
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
relation -> predicate (__ term):* {% (d) => {return [d[0], d[1].map(t => t[1])]} %}

# , | ;
# p2 x y, p1 z, foo
pureQuery -> null {% () => [] %}
pureQuery -> relation {% (d) => [d[0]] %}
pureQuery -> relation _ "," _ pureQuery {% (d) => [d[0]].concat(d[4]) %}

# foo x | after (rel a, rel b)
operation -> relation {% (d) => { return [{ tag: "rel", pattern: d[0] }] } %}
operation -> fnCall {% (d) => ([{ tag: "call", value:  d[0] }]) %}
operation -> "after" _  "(" _ pureQuery _ ")" {% (d) => { return d[4].map((r) => ({ tag: "after", pattern: r })) } %}
operation -> "before" _ "(" _ pureQuery _ ")" {% (d) => { return d[4].map((r) => ({ tag: "before", pattern: r })) } %}
# (TODO: other quantifiers)
operation -> "choose" _ "[exactly 1]" _ "(" _ pureQuery _ ")"
  {% (d) => {
    return [
        {tag: 'subQuery', name: '_choices', body: d[6] },
        {tag: 'takeChoice'}
    ]
  } %}
operation -> var _ "=" _ "count" _ "(" _ pureQuery _ ")"
  {% (d) => {
    return[
        {tag: 'countQuery', name: d[0], body: d[8] },
    ];
  } %}
operation -> term _ "<" _ term
  {% (d) => {
    return[
        {tag: 'binOp', operator: d[2], l: d[0], r: d[4]}
    ];
  } %}

operation -> term _ "=" _ term
  {% (d) => {
    return[
        {tag: 'binOp', operator: d[2], l: d[0], r: d[4]}
    ];
  } %}

separator -> "," {% id %}
separator -> ";" {% id %}

# foo x, after (rel a, rel b)
line -> null {% () => [] %}
line -> operation separator:?
  {% (d) => {
    d[0].sep = d[1] ? d[1] : ",";
    return d[0];
  } %}
line -> operation _ separator _ line
  {% (d) => {
    d[0].sep = d[2];
    return d[0].concat(d[4])
  } %}

# rule-name (action a): foo a, bar a b.
rule -> identifier:? _ "(" _ pureQuery _ "):" _ line _ "." {%
  (d) => {
      return {
          guard: d[4],
          body: [d[8]],
          name: d[0] ? d[0] : "(anonymous rule)",
          ruleText: "",
      };
  } %}

program -> (_ rule _):* {% (d) => d[0].map((r) => r[1]) %}

# whitespace
_ -> null | _ [\s] {% function() {} %}
__ -> [\s] | __ [\s] {% function() {} %}

# new syntax

event_expr -> "." {% (d) => ({ tag: "done"}) %}
event_expr -> identifier {% (d) => ({ tag: "literal", name: d[0]}) %}
event_expr -> "(" _ event_expr _ ")" {% (d) => d[2] %}
event_expr -> event_expr _ "," _ event_expr  {% (d) => ({ tag: "concurrent", a: d[0], b: d[4]}) %}
event_expr -> event_expr _ "->" _ event_expr  {% (d) => ({ tag: "sequence", a: d[0], b: d[4]}) %}
event_expr -> "[" _ event_expr _ "|" "]" {% (d) => ({ tag: "with-tuples", body: d[2], tuples: {}}) %}
