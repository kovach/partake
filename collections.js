/* Utility functions and collection types. */

let ap = Symbol("partial-apply");
Function.prototype[ap] = function (...given) {
  return (...args) => this.apply(this, given.concat(args));
};
function assert(cond, msg = "") {
  if (!cond) {
    if (typeof msg === "function") msg = msg();
    throw new Error(msg);
  }
}

Array.prototype.sum = function () {
  return this.reduce((a, b) => a + b, 0);
};

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

function range(n) {
  return [...Array(n).keys()];
}
function unzip(arr) {
  let as = [];
  let bs = [];
  for (let [a, b] of arr) {
    as.push(a);
    bs.push(b);
  }
  return [as, bs];
}

function zip(as, bs) {
  let result = [];
  for (let i = 0; i < Math.min(as.length, bs.length); i++) result.push([as[i], bs[i]]);
  return result;
}
function enumerate(xs) {
  return zip(range(xs.length), xs);
}

function splitArray(arr) {
  assert(arr.length > 0);
  return [arr[0], arr.slice(1)];
}

Array.prototype.split = function () {
  return splitArray(this);
};

Map.prototype.map = function (f) {
  let m = new Map();
  for (let [key, val] of this.entries()) {
    m.set(key, f(val));
  }
  return m;
};

class KeyedMap {
  constructor(key, values = []) {
    this.key = key;
    this.map = new Map();
    for (let [k, v] of values) this.set(k, v);
  }
  get(k) {
    let m = this.map.get(this.key(k));
    return m ? m[1] : undefined;
  }
  contains(k) {
    return this.map.has(this.key(k));
  }
  set(k, v) {
    this.map.set(this.key(k), [k, v]);
  }
  delete(k) {
    this.map.delete(this.key(k));
  }
  *entries() {
    for (let x of this.map.values()) yield x;
  }
}

class MonoidMap {
  constructor(zero, plus, map) {
    this.map = map || new Map();
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
  clone() {
    let entries = Array.from(this.map.entries());
    //return new MonoidMap(this.zero, this.plus, new Map(structuredClone(entries)));
    return new MonoidMap(this.zero, this.plus, new Map(entries));
  }
  update(key, fn) {
    this.map.set(key, fn(this.get(key)));
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
export {
  ap,
  toTag,
  assert,
  splitArray,
  MonoidMap,
  ArrayMap,
  KeyedMap,
  DelayedMap,
  range,
  unzip,
  zip,
  enumerate,
};
