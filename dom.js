import { assert, ArrayMap } from "./collections.js";
import { Binding } from "./binding.js";

function getId(id) {
  return document.getElementById(id);
}
function create(type, ...children) {
  let e = document.createElement(type);
  children.forEach((c) => e.appendChild(c));
  return e;
}
function remove(child) {
  assert(child !== null, "remove");
  let maybeParent = child.parentNode;
  if (maybeParent) maybeParent.removeChild(child);
}
function childParent(child, parent) {
  remove(child);
  parent.appendChild(child);
  return child;
}
function createChild(type, parent) {
  return childParent(create(type), parent);
}
function createChildId(type, id) {
  return createChild(type, getId(id));
}
function* allChildren(node) {
  yield node;
  for (let child of node.children) {
    for (let e of allChildren(child)) {
      yield e;
    }
  }
}
function createText(str) {
  let e = create("pre");
  e.innerHTML = str;
  return e;
}

function createSpace() {
  let e = create("pre");
  e.style.height = "1em";
  return e;
}

function flex(orientiation, ...children) {
  let e = create("div");
  e.style.display = "flex";
  e.style["flex-direction"] = orientiation;
  children.forEach((c) => childParent(c, e));
  return e;
}

function renderJSON(json) {
  switch (jsonType(json)) {
    case "array":
      return renderArray(json);
    case "object":
      return renderObj(json);
    case "map":
      return renderObj(Object.fromEntries(json.map));
    case "binding":
      return renderObj({
        substitution: Object.fromEntries(json.substitution),
        notes: Object.fromEntries(json.notes.map),
      });
    case "string":
      return createText(JSON.stringify(json));
    case "number":
      return createText(json);
  }
}
function jsonType(x) {
  if (Array.isArray(x)) return "array";
  if (typeof x === "string") return "string";
  if (typeof x === "number") return "number";
  if (x instanceof Map || x instanceof ArrayMap) return "map";
  if (x instanceof Binding) return "binding";
  return "object";
}

function renderArray(arr, orientation = null) {
  orientation = orientation || (arr.length > 5 ? "column" : "row");
  arr = arr.map((el) => renderJSON(el));
  arr = between(arr, () => createText(", "));
  return flex(orientation, createText("["), ...arr, createText("]"));
}
function withClass(e, ...names) {
  names.forEach((name) => e.classList.add(name));
  return e;
}
function renderObj(obj) {
  if (JSON.stringify(obj).length < 40) {
    return flex(
      "row",
      withClass(createText("{"), "fix"),
      ...between(
        Object.keys(obj).map((k) => renderKeyVal(k, obj[k])),
        () => createText(", ")
      ),
      withClass(createText("}"), "fix")
    );
  }
  return flex(
    "row",
    flex(
      "column",
      withClass(createText("{"), "fix"),
      withClass(createText(""), "grow"),
      withClass(createText("}"), "fix")
    ),
    flex(
      "column",
      createSpace(),
      ...Object.keys(obj).map((k) => renderKeyVal(k, obj[k])),
      createText(",")
    )
  );
}
function renderKeyVal(key, val) {
  let e = flex("row", createText(key + ":"), renderJSON(val));
  return e;
}

function between(arr, sep) {
  let result = [];
  arr.forEach((e, i) => {
    result.push(e);
    if (i < arr.length - 1) result.push(sep());
  });
  return result;
}

class SVGHelp {
  create(type) {
    return document.createElementNS("http://www.w3.org/2000/svg", type);
  }
  createChild(type, parent) {
    return childParent(this.create(type), parent);
  }
  createChildId(type, id) {
    return this.createChild(type, getId(id));
  }
  createElement(tag, id) {
    let e = this.create(tag);
    e.id = id;
    return e;
  }
  set(e, key, val) {
    return e.setAttribute(key, val);
  }
  mkRectangle(x, y, width = 100, height = 100) {
    let e = s.createChildId("rect", "svg");
    s.set(e, "width", width);
    s.set(e, "height", height);
    s.set(e, "x", x);
    s.set(e, "y", y);
    s.set(e, "fill", "#ffeeaa");
    return e;
  }

  mkCircle() {
    let e = s.createChildId("circle", "svg");
    s.set(e, "r", "30");
    s.set(e, "cx", "30");
    s.set(e, "cy", "30");
    s.set(e, "fill", "#ffeeaa");
    return e;
  }
}
let s = new SVGHelp();

export {
  s,
  getId,
  create,
  remove,
  childParent,
  createChild,
  createChildId,
  allChildren,
  createText,
  renderJSON,
  flex,
  withClass,
};
