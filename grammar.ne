@preprocessor module

main -> line {% id %}

# var, Var
var -> [a-zA-Z] [a-zA-Z0-9']:*  {% (d) => d[0] + d[1].join("") %}
# a2bc'
predicate -> [a-z] [a-zA-Z0-9']:* {% (d) => d[0] + d[1].join("") %}

literal -> var {% id %}
literal -> [0-9]:+ {% (d) => parseInt(d[0].join("")) %}

# pred2 x y -> ["pred", ["x", "y"]]
relation -> predicate (__ literal):* {% (d) => {return [d[0], d[1].map(t => t[1])]} %}

# p2 x y, p1 z, foo
pureQuery -> null {% () => [] %}
pureQuery -> relation {% (d) => [d[0]] %}
pureQuery -> relation _ "," _ pureQuery {% (d) => [d[0]].concat(d[4]) %}

# foo x | after (rel a, rel b)
operation -> relation {% (d) => { return [{ tag: "rel", pattern: d[0] }] } %}
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
operation -> literal _ "<" _ literal
  {% (d) => {
    return[
        {tag: 'binOp', operator: d[2], l: d[0], r: d[4]}
    ];
  } %}

# foo x, after (rel a, rel b)
line -> null {% () => [] %}
line -> operation {% id %}
line -> operation _ "," _ line {% (d) => d[0].concat(d[4]) %}

# whitespace
_ -> null | _ [\s] {% function() {} %}
__ -> [\s] | __ [\s] {% function() {} %}