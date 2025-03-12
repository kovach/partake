import { assert, MonoidMap } from "./collections.js";

// both inclusive
function randRange(a, b) {
  return a + Math.floor(Math.random() * (1 + b - a));
}
function randNat(n) {
  return randRange(1, n);
}
function randomSample(array, count) {
  let n = array.length;
  count = Math.min(n, count);
  array = [...array];
  for (let i = 0; i < count; i++) {
    let j = randRange(i, n - 1);
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

export { hist, repeat, randRange, randNat, randomSample };
