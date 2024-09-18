function assert(cond, msg) {
  if (!cond) throw new Error(msg);
}

function getId(id) {
  return document.getElementById(id);
}
function create(type) {
  let e = document.createElement(type);
  childParent(e, getId("body"));
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
function createElement(tag, id) {
  let e = create(tag);
  e.id = id;
  return e;
}
function* allChildren(node) {
  yield node;
  for (let child of node.children) {
    for (let e of allChildren(child)) {
      yield e;
    }
  }
}

class SVGHelp {
  create(type) {
    return document.createElementNS("http://www.w3.org/2000/svg", type);
  }
  createChild(type, parent) {
    return childParent(this.create(type), parent);
  }
  createChildId(type, id) {
    return createChild(type, getId(id));
  }
  createElement(tag, id) {
    let e = this.create(tag);
    e.id = id;
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
  createElement,
  allChildren,
};
