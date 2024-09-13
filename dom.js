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
  assert(child !== null, `${child}, ${parent}`);
  let maybeParent = child.parentNode;
  if (maybeParent) maybeParent.removeChild(child);
}
function childParent(child, parent) {
  remove(child);
  parent.appendChild(child);
  return child;
}
function createChildElem(type, parent) {
  return childParent(create(type), parent);
}
function createChildId(type, id) {
  return createChildElem(type, getId(id));
}
function createElement(tag, id) {
  let e = create(tag);
  e.id = id;
  return e;
}

export {
  getId,
  create,
  remove,
  childParent,
  createChildElem,
  createChildId,
  createElement,
};
