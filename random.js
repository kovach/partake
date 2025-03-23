import { assert, MonoidMap } from "./collections.js";

// both inclusive
function randRange(a, b, rng = jsf) {
  return a + Math.floor(rng() * (1 + b - a));
}
function randNat(n, rng = jsf) {
  return randRange(1, n);
}
function randomSample(array, count, rng = jsf) {
  let n = array.length;
  count = Math.min(n, count);
  array = [...array];
  for (let i = 0; i < count; i++) {
    let j = randRange(i, n - 1);
    console.log("j: ", j);
    let tmp = array[i];
    array[i] = array[j];
    array[j] = tmp;
  }
  return array.slice(0, count);
}

function repeat(fn, n) {
  for (let i = 0; i < n; i++) {
    fn();
  }
}

function hist(fn, n) {
  let m = new MonoidMap(
    () => ({ i: 0 }),
    (a, v) => (a.i += v)
  );
  repeat(() => m.add(fn(), 1), n);
  return m;
}

let a = 7;
let b = 7;
let c = 7;
let d = 7;

// modified from https://github.com/bryc/code/blob/master/jshash/PRNGs.md
function jsf() {
  a |= 0;
  b |= 0;
  c |= 0;
  d |= 0;
  let t = (a - ((b << 23) | (b >>> 9))) | 0;
  a = (b ^ ((c << 16) | (c >>> 16))) | 0;
  b = (c + ((d << 11) | (d >>> 21))) | 0;
  b = (c + d) | 0;
  c = (d + t) | 0;
  d = (a + t) | 0;
  return (d >>> 0) / 4294967296;
}

function resetSeed() {
  a = 7;
  b = 7;
  c = 7;
  d = 7;
}

// Seed procedure as recommended by the author:
//let seed = 7; // any unsigned 32-bit integer.
//let jsf = jsf32b(0xf1ea5eed, seed, seed, seed);

export { hist, repeat, randRange, randNat, randomSample, jsf, resetSeed };
