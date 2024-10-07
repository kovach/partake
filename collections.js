function assert(cond, msg) {
  if (!cond) throw new Error(msg);
}

class MonoidMap {
  constructor(zero, plus, values) {
    this.map = new Map(values);
    this.zero = zero;
    this.plus = plus;
  }
  get(key) {
    let v = this.map.get(key);
    if (v === undefined) {
      v = this.zero();
      this.map.set(key, v);
    }
    return v;
  }
  add(key, value) {
    let v = this.get(key);
    this.plus(v, value);
    return v;
  }
}

class ArrayMap extends MonoidMap {
  constructor(values) {
    super(
      () => [],
      (a, b) => a.push(b),
      values
    );
  }
}

export { assert, MonoidMap, ArrayMap };
