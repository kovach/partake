class MonoidMap {
  constructor(zero, plus) {
    this.map = new Map();
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
  constructor() {
    super(
      () => [],
      (a, b) => a.push(b)
    );
  }
}

export { MonoidMap, ArrayMap };
