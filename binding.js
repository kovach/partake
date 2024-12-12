import { ArrayMap } from "./collections.js";

function cloneTerm(term) {
  switch (term.tag) {
    case "var":
    case "sym":
    case "int":
      return structuredClone(term);
    case "set":
      return { tag: "set", value: term.value.map((b) => b.clone()) };
    default:
      throw "";
  }
}
class Binding {
  substitution = new Map();
  notes = new ArrayMap();
  parent = null;

  constructor(parent = null) {
    this.parent = parent;
  }

  toJSON() {
    return "a binding";
  }

  *[Symbol.iterator]() {
    for (let k of this.substitution.keys()) yield k;
    if (this.parent) for (let k of this.parent) yield k;
  }

  clone() {
    let m = new Binding();
    m.parent = this.parent;
    //m.notes = new ArrayMap( new Map(structuredClone(Array.from(this.notes.map.entries()))));
    m.notes = this.notes.clone();
    m.substitution = this.substitution.map(cloneTerm);
    return m;
  }

  extend() {
    return new Binding(this);
  }

  // shadows parent
  set(key, val) {
    this.substitution.set(key, val);
    return this;
  }
  get(key) {
    let r = this.substitution.get(key);
    if (r !== undefined) return r;
    if (this.parent) return this.parent.get(key);
  }
  has(key) {
    return this.get(key) !== undefined;
  }
  parent() {
    return this.parent;
  }
  eq(b) {
    for (let [key, val] of this.substitution.entries()) {
      if (b.get(key) !== val) return false;
    }
    return true;
  }
}

export { Binding };
