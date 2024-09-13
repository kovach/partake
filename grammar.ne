@preprocessor module

main -> line {% id %}
statement -> "foo" | "bar"

var -> [a-zA-Z] [a-zA-Z]:*  {% (d) => d[0] + d[1].join("") %}
predicate -> [a-z] [a-zA-Z]:* {% (d) => d[0] + d[1].join("") %}
relation -> predicate (__ var):* {% (d) => {return [d[0], d[1].map(t => t[1])]} %}

pureQuery -> null {% () => [] %}
pureQuery -> relation {% (d) => [d[0]] %}
pureQuery -> relation _ "," _ pureQuery {% (d) => [d[0]].concat(d[4]) %}

operation -> relation {% (d) => { return [{ tag: "rel", pattern: d[0] }] } %}
operation -> "after" _  "(" _ pureQuery _ ")" {% (d) => { return d[4].map((r) => ({ tag: "after", pattern: r })) } %}
operation -> "before" _ "(" _ pureQuery _ ")" {% (d) => { return d[4].map((r) => ({ tag: "before", pattern: r })) } %}
line -> null {% () => [] %}
line -> operation {% id %}
line -> operation _ "," _ line {% (d) => d[0].concat(d[4]) %}

# Whitespace
_ -> null | _ [\s] {% function() {} %}
__ -> [\s] | __ [\s] {% function() {} %}

# foo X, after (bar, baz X)