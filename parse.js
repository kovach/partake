import grammar from "./grammar.js";
import { assert } from "./collections.js";

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

export { parseNonterminal };
