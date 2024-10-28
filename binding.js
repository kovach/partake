import { ArrayMap } from "./collections.js";

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
    m.notes = new ArrayMap(structuredClone(Array.from(this.notes.map.entries())));
    m.substitution = this.substitution.map(structuredClone);
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
}

export { Binding };
