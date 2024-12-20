/* Utility functions and collection types. */

function assert(cond, msg = "") {
  if (!cond) throw new Error(msg);
}

// use like this:
//   let x = toTag(f)
//   ... x`some string` ...
function toTag(f) {
  return ([str]) => f(str);
}
function arrayUpdate(arr, f) {
  for (let i = 0; i < arr.length; i++) {
    arr[i] = f(arr[i]);
  }
  return arr;
}
// implement early exit behavior
function forEach(arr, f) {
  for (let i = 0; i < arr.length; i++) {
    if (f(arr[i], i)) return true;
  }
  return false;
}

function splitArray(arr) {
  assert(arr.length > 0);
  return [arr[0], arr.slice(1)];
}

Map.prototype.map = function (f) {
  let m = new Map();
  for (let [key, val] of this.entries()) {
    m.set(key, f(val));
  }
  return m;
};

class MonoidMap {
  constructor(zero, plus, values) {
    this.map = new Map(values);
    this.zero = zero;
    this.plus = plus;
  }
  reset(key) {
    let v = this.zero();
    this.map.set(key, v);
    return v;
  }
  get(key) {
    let v = this.map.get(key);
    if (v === undefined) v = this.reset(key);
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

class DelayedMap {
  map;
  callbacks;
  constructor(values) {
    this.map = new Map(values);
    this.callbacks = new ArrayMap();
  }
  get(key, fn) {
    let v = this.map.get(key);
    if (v === undefined) {
      this.callbacks.add(key, fn);
    } else {
      fn(v);
    }
  }
  set(key, value) {
    this.map.set(key, value);
    let v = this.map.get(key);
    let fns = this.callbacks.get(key);
    while (fns.length > 0) {
      fns.pop()(value);
    }
  }
}
export { assert, splitArray, MonoidMap, ArrayMap, DelayedMap };
