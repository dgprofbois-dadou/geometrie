'use strict';

// ══════════════════════════════════════════════════════
// GEOMETRY ENGINE
// ══════════════════════════════════════════════════════

const canvas = document.getElementById('geo-canvas');
const ctx = canvas.getContext('2d');

// ── State ──────────────────────────────────────────
const state = {
  tool: 'select',
  objects: [],          // all geo objects
  selected: [],         // selected object ids
  hover: null,          // hovered object id
  tempPoints: [],       // points accumulated for multi-click tools
  undoStack: [],
  redoStack: [],
  // viewport
  ox: 0, oy: 0,         // canvas centre in world coords
  scale: 60,            // pixels per unit
  showGrid: true,
  showAxes: true,
  // pan
  isPanning: false,
  panStart: null,
  // drag
  isDragging: false,
  dragTarget: null,
  dragOffsetWorld: null,
  dragLastWorld: null,  // for non-point drag (delta-based)
  // lasso
  isLasso: false,
  lassoStart: null,
  lassoEnd: null,
  // zones (orthographic projection)
  zonesVisible: false,
  zones: [],          // [{id, label, x1,y1,x2,y2, state:'neutral'|'active'|'yellow'|'green'}]
  // figure groups (drag-and-drop)
  figureGroups: [],   // [{id, label, objectIds, pivotId, targetZoneId, targetX, targetY}]
  isDraggingGroup: null,  // group id being dragged
  groupDragOffset: null,  // {dx, dy} world offset
  groupDragOrigPos: null, // {x,y} original pivot position
  groupMovedCallback: null,
  // label counter
  labelCounters: { point: 0, line: 0, circle: 0, polygon: 0, text: 0, angle: 0, measure: 0 },
  editingGroupId: null,  // group currently being edited at detail level
  exerciseMode: false    // true only during exercise playback (controls zone feedback)
};

let nextId = 1;
function uid() { return nextId++; }

// ── Label generators ──────────────────────────────
const POINT_LABELS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
function nextPointLabel() {
  const i = state.labelCounters.point % 26;
  const n = Math.floor(state.labelCounters.point / 26);
  state.labelCounters.point++;
  return POINT_LABELS[i] + (n > 0 ? String(n) : '');
}
function nextLineLabel() { return 'g' + (++state.labelCounters.line); }
function nextCircleLabel() { return 'c' + (++state.labelCounters.circle); }
function nextPolygonLabel() { return 'p' + (++state.labelCounters.polygon); }
function nextAngleLabel() { return 'α' + (++state.labelCounters.angle); }
function nextMeasureLabel() { return 'd' + (++state.labelCounters.measure); }

// ── Coordinate helpers ────────────────────────────
function worldToCanvas(wx, wy) {
  return {
    x: canvas.width / 2 + (wx - state.ox) * state.scale,
    y: canvas.height / 2 - (wy - state.oy) * state.scale
  };
}
function canvasToWorld(cx, cy) {
  return {
    x: state.ox + (cx - canvas.width / 2) / state.scale,
    y: state.oy - (cy - canvas.height / 2) / state.scale
  };
}

// ── Math helpers ──────────────────────────────────
const dist = (a, b) => Math.hypot(b.x - a.x, b.y - a.y);
const midpoint = (a, b) => ({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 });
const dot = (a, b) => a.x * b.x + a.y * b.y;
const cross2d = (a, b) => a.x * b.y - a.y * b.x;

function lineIntersect(p1, d1, p2, d2) {
  const denom = cross2d(d1, d2);
  if (Math.abs(denom) < 1e-10) return null;
  const t = cross2d({ x: p2.x - p1.x, y: p2.y - p1.y }, d2) / denom;
  return { x: p1.x + t * d1.x, y: p1.y + t * d1.y };
}

function circumcenter(a, b, c) {
  const ax = b.x - a.x, ay = b.y - a.y;
  const bx = c.x - a.x, by = c.y - a.y;
  const D = 2 * (ax * by - ay * bx);
  if (Math.abs(D) < 1e-10) return null;
  const ux = (by * (ax * ax + ay * ay) - ay * (bx * bx + by * by)) / D;
  const uy = (ax * (bx * bx + by * by) - bx * (ax * ax + ay * ay)) / D;
  return { x: a.x + ux, y: a.y + uy };
}

function signedAngle(cx, cy, ax, ay, bx, by) {
  const d1x = ax - cx, d1y = ay - cy;
  const d2x = bx - cx, d2y = by - cy;
  let a = Math.atan2(cross2d({ x: d1x, y: d1y }, { x: d2x, y: d2y }),
                     dot({ x: d1x, y: d1y }, { x: d2x, y: d2y }));
  return a * 180 / Math.PI;
}

// ── Object types ──────────────────────────────────
// Each object: { id, type, label, color, lineWidth, visible, ...typeSpecific }
// Point: { x, y, fixed }
// Segment/Line/Ray/Vector: { p1id, p2id }  (p1id/p2id = point ids)
// Circle: { centerId, radiusPointId } or { centerId, r } for fixed
// Circle3pts: { p1id, p2id, p3id }
// Polygon: { pointIds[] }
// Angle: { p1id, vertexId, p2id, value (computed) }
// Distance: { p1id, p2id, value }
// Area: { polygonId, value }
// Text: { x, y, text }
// Parallel/Perp/Bisector/etc.: derived lines stored as type='line' with deps

function getObj(id) { return state.objects.find(o => o.id === id); }
function getPoint(id) { const o = getObj(id); return o ? { x: o.x, y: o.y } : null; }

// Returns the direction vector {dx, dy} of any line-like object (world coords)
function getLineDirection(ref) {
  if (!ref) return null;
  if (ref.p1id && ref.p2id) {
    const p1 = getPoint(ref.p1id), p2 = getPoint(ref.p2id);
    if (p1 && p2) return { dx: p2.x - p1.x, dy: p2.y - p1.y };
  }
  // Derived line: direction already stored as dx/dy
  if (ref.dx != null && (ref.dx !== 0 || ref.dy !== 0)) return { dx: ref.dx, dy: ref.dy };
  return null;
}

function evalObject(obj) {
  // Compute derived positions / values
  if (!obj) return;
  switch (obj.type) {
    case 'midpoint': {
      const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
      if (p1 && p2) { obj.x = (p1.x + p2.x) / 2; obj.y = (p1.y + p2.y) / 2; }
      break;
    }
    case 'circle3pts': {
      const a = getPoint(obj.p1id), b = getPoint(obj.p2id), c = getPoint(obj.p3id);
      if (a && b && c) {
        const cc = circumcenter(a, b, c);
        if (cc) { obj.cx = cc.x; obj.cy = cc.y; obj.r = dist(cc, a); }
      }
      break;
    }
    case 'circle': {
      if (obj.radiusPointId) {
        const c = getPoint(obj.centerId), p = getPoint(obj.radiusPointId);
        if (c && p) obj.r = dist(c, p);
      }
      break;
    }
    case 'parallel': {
      const ref = getObj(obj.refLineId);
      const pt = getPoint(obj.pointId);
      if (ref && pt) {
        const dir = getLineDirection(ref);
        if (dir) { obj.dx = dir.dx; obj.dy = dir.dy; obj.px = pt.x; obj.py = pt.y; }
      }
      break;
    }
    case 'perpendicular': {
      const ref = getObj(obj.refLineId);
      const pt = getPoint(obj.pointId);
      if (ref && pt) {
        const dir = getLineDirection(ref);
        if (dir) { obj.dx = -dir.dy; obj.dy = dir.dx; obj.px = pt.x; obj.py = pt.y; }
      }
      break;
    }
    case 'perp-bisector': {
      const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
      if (p1 && p2) {
        obj.px = (p1.x + p2.x) / 2; obj.py = (p1.y + p2.y) / 2;
        obj.dx = -(p2.y - p1.y); obj.dy = p2.x - p1.x;
      }
      break;
    }
    case 'angle-bisector': {
      const v = getPoint(obj.vertexId), a = getPoint(obj.p1id), b = getPoint(obj.p2id);
      if (v && a && b) {
        const d1 = dist(v, a), d2 = dist(v, b);
        if (d1 > 1e-9 && d2 > 1e-9) {
          obj.px = v.x; obj.py = v.y;
          obj.dx = (a.x - v.x) / d1 + (b.x - v.x) / d2;
          obj.dy = (a.y - v.y) / d1 + (b.y - v.y) / d2;
        }
      }
      break;
    }
    case 'reflect-line': {
      const refLine = getObj(obj.refLineId);
      const src = getObj(obj.sourceId);
      if (!refLine || !src) break;
      const rp1 = getPoint(refLine.p1id), rp2 = getPoint(refLine.p2id);
      if (!rp1 || !rp2) break;
      if (src.type === 'point' || src.type === 'midpoint') {
        const p = { x: src.x, y: src.y };
        const r = reflectOverLine(p, rp1, rp2);
        obj.x = r.x; obj.y = r.y;
      }
      break;
    }
    case 'reflect-point': {
      const center = getPoint(obj.centerId);
      const src = getObj(obj.sourceId);
      if (!center || !src) break;
      if (src.type === 'point' || src.type === 'midpoint') {
        obj.x = 2 * center.x - src.x;
        obj.y = 2 * center.y - src.y;
      }
      break;
    }
    case 'rotate': {
      const center = getPoint(obj.centerId);
      const src = getObj(obj.sourceId);
      if (!center || !src) break;
      if (src.type === 'point' || src.type === 'midpoint') {
        const dx = src.x - center.x, dy = src.y - center.y;
        const a = obj.angle * Math.PI / 180;
        obj.x = center.x + dx * Math.cos(a) - dy * Math.sin(a);
        obj.y = center.y + dx * Math.sin(a) + dy * Math.cos(a);
      }
      break;
    }
    case 'translate': {
      const v1 = getPoint(obj.vec1Id), v2 = getPoint(obj.vec2Id);
      const src = getObj(obj.sourceId);
      if (!v1 || !v2 || !src) break;
      if (src.type === 'point' || src.type === 'midpoint') {
        obj.x = src.x + (v2.x - v1.x);
        obj.y = src.y + (v2.y - v1.y);
      }
      break;
    }
    case 'intersect': {
      const l1 = getObj(obj.l1id), l2 = getObj(obj.l2id);
      if (!l1 || !l2) break;
      const ip = computeIntersect(l1, l2);
      if (ip) { obj.x = ip.x; obj.y = ip.y; }
      break;
    }
    case 'angle-measure': {
      const v = getPoint(obj.vertexId), a = getPoint(obj.p1id), b = getPoint(obj.p2id);
      if (v && a && b) {
        let ang = signedAngle(v.x, v.y, a.x, a.y, b.x, b.y);
        if (ang < 0) ang += 360;
        obj.value = ang;
      }
      break;
    }
    case 'distance-measure': {
      const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
      if (p1 && p2) obj.value = dist(p1, p2);
      break;
    }
    case 'area-measure': {
      const poly = getObj(obj.polygonId);
      if (poly) obj.value = polygonArea(poly.pointIds);
      break;
    }
  }
}

function reflectOverLine(p, a, b) {
  const dx = b.x - a.x, dy = b.y - a.y;
  const len2 = dx * dx + dy * dy;
  if (len2 < 1e-10) return p;
  const t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / len2;
  const fx = a.x + t * dx, fy = a.y + t * dy;
  return { x: 2 * fx - p.x, y: 2 * fy - p.y };
}

function polygonArea(ids) {
  let area = 0;
  const pts = ids.map(getPoint).filter(Boolean);
  for (let i = 0; i < pts.length; i++) {
    const j = (i + 1) % pts.length;
    area += pts[i].x * pts[j].y - pts[j].x * pts[i].y;
  }
  return Math.abs(area) / 2;
}

function computeIntersect(l1, l2) {
  const linePoints = (o) => {
    if (o.p1id && o.p2id) {
      const p1 = getPoint(o.p1id), p2 = getPoint(o.p2id);
      if (!p1 || !p2) return null;
      return { p: p1, d: { x: p2.x - p1.x, y: p2.y - p1.y } };
    }
    if (o.px != null) return { p: { x: o.px, y: o.py }, d: { x: o.dx, y: o.dy } };
    return null;
  };
  const ld1 = linePoints(l1), ld2 = linePoints(l2);
  if (!ld1 || !ld2) return null;
  return lineIntersect(ld1.p, ld1.d, ld2.p, ld2.d);
}

function evalAll() {
  // Multi-pass to handle dependency chains
  for (let pass = 0; pass < 3; pass++) {
    state.objects.forEach(evalObject);
  }
}

// ── Hit testing ───────────────────────────────────
const HIT_RADIUS_PX = 10;

function hitTestPoint(obj, cx, cy) {
  if (obj.type !== 'point' && obj.type !== 'midpoint' && obj.type !== 'reflect-line' &&
      obj.type !== 'reflect-point' && obj.type !== 'rotate' && obj.type !== 'translate' &&
      obj.type !== 'intersect') return false;
  const c = worldToCanvas(obj.x, obj.y);
  return Math.hypot(cx - c.x, cy - c.y) <= HIT_RADIUS_PX;
}

function hitTestSegment(p1w, p2w, cx, cy) {
  const p1 = worldToCanvas(p1w.x, p1w.y);
  const p2 = worldToCanvas(p2w.x, p2w.y);
  const dx = p2.x - p1.x, dy = p2.y - p1.y;
  const len2 = dx * dx + dy * dy;
  if (len2 < 1e-6) return Math.hypot(cx - p1.x, cy - p1.y) <= HIT_RADIUS_PX;
  const t = Math.max(0, Math.min(1, ((cx - p1.x) * dx + (cy - p1.y) * dy) / len2));
  return Math.hypot(cx - (p1.x + t * dx), cy - (p1.y + t * dy)) <= HIT_RADIUS_PX;
}

function hitTestInfiniteLine(px, py, dx, dy, cx, cy) {
  // Project onto line
  const len2 = dx * dx + dy * dy;
  if (len2 < 1e-6) return false;
  const t = ((cx - px) * dx + (cy - py) * dy) / len2;
  return Math.hypot(cx - (px + t * dx), cy - (py + t * dy)) <= HIT_RADIUS_PX;
}

function hitTestCircle(cw, r, cx, cy) {
  const cc = worldToCanvas(cw.x, cw.y);
  const rPx = r * state.scale;
  const d = Math.hypot(cx - cc.x, cy - cc.y);
  return Math.abs(d - rPx) <= HIT_RADIUS_PX;
}

function objectAtCanvas(cx, cy, preferPoints = false) {
  // In select mode, check points first so endpoint clicks grab the point, not the parent line
  if (preferPoints) {
    for (let i = state.objects.length - 1; i >= 0; i--) {
      const obj = state.objects[i];
      if (!obj.visible) continue;
      if (obj.type !== 'point' && obj.type !== 'midpoint' && obj.type !== 'intersect' &&
          obj.type !== 'reflect-line' && obj.type !== 'reflect-point' &&
          obj.type !== 'rotate' && obj.type !== 'translate') continue;
      if (hitTestObject(obj, cx, cy)) return obj;
    }
  }
  // Check in reverse order (topmost first)
  for (let i = state.objects.length - 1; i >= 0; i--) {
    const obj = state.objects[i];
    if (!obj.visible) continue;
    if (obj.type === 'group') continue;
    if (hitTestObject(obj, cx, cy)) return obj;
  }
  return null;
}

function hitTestObject(obj, cx, cy) {
  switch (obj.type) {
    case 'point':
    case 'midpoint':
    case 'reflect-line':
    case 'reflect-point':
    case 'rotate':
    case 'translate':
    case 'intersect':
      return hitTestPoint(obj, cx, cy);
    case 'segment':
    case 'vector': {
      const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
      if (!p1 || !p2) return false;
      return hitTestSegment(p1, p2, cx, cy);
    }
    case 'line':
    case 'ray': {
      const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
      if (!p1 || !p2) return false;
      const c1 = worldToCanvas(p1.x, p1.y), c2 = worldToCanvas(p2.x, p2.y);
      return hitTestInfiniteLine(c1.x, c1.y, c2.x - c1.x, c2.y - c1.y, cx, cy);
    }
    case 'parallel':
    case 'perpendicular':
    case 'perp-bisector':
    case 'angle-bisector': {
      if (obj.px == null) return false;
      const c = worldToCanvas(obj.px, obj.py);
      return hitTestInfiniteLine(c.x, c.y, obj.dx * state.scale, -obj.dy * state.scale, cx, cy);
    }
    case 'circle': {
      const cen = getPoint(obj.centerId);
      if (!cen) return false;
      return hitTestCircle(cen, obj.r, cx, cy);
    }
    case 'circle3pts': {
      if (obj.cx == null) return false;
      return hitTestCircle({ x: obj.cx, y: obj.cy }, obj.r, cx, cy);
    }
    case 'semicircle': {
      const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
      if (!p1 || !p2) return false;
      const c = midpoint(p1, p2);
      return hitTestCircle(c, dist(p1, p2) / 2, cx, cy);
    }
    case 'arc': {
      const center = getPoint(obj.centerId);
      if (!center || obj.r == null) return false;
      return hitTestCircle(center, obj.r, cx, cy);
    }
    case 'polygon':
    case 'rect': {
      // hit-test edges OR filled interior (for rect with fillOpacity > 0)
      const pts = obj.pointIds.map(getPoint).filter(Boolean);
      if (obj.type === 'rect' && (obj.fillOpacity || 0) > 0.01 && pts.length >= 4) {
        // Check if inside rectangle
        const world = canvasToWorld(cx, cy);
        const xs = pts.map(p => p.x), ys = pts.map(p => p.y);
        if (world.x >= Math.min(...xs) && world.x <= Math.max(...xs) &&
            world.y >= Math.min(...ys) && world.y <= Math.max(...ys)) return true;
      }
      for (let i = 0; i < pts.length; i++) {
        if (hitTestSegment(pts[i], pts[(i + 1) % pts.length], cx, cy)) return true;
      }
      return false;
    }
    case 'text': {
      const c = worldToCanvas(obj.x, obj.y);
      return Math.abs(cx - c.x) < 60 && Math.abs(cy - c.y) < 12;
    }
    case 'angle-measure': {
      const v = getPoint(obj.vertexId);
      if (!v) return false;
      return hitTestPoint({ type: 'point', x: v.x, y: v.y }, cx, cy);
    }
    case 'group': return false;
    default: return false;
  }
}

function isPointLike(obj) {
  return ['point', 'midpoint', 'reflect-line', 'reflect-point', 'rotate', 'translate', 'intersect'].includes(obj?.type);
}

function getObjectGroupId(objId) {
  const obj = getObj(objId);
  return obj ? obj.groupId || null : null;
}
function getGroup(groupId) {
  return state.objects.find(o => (o.type === 'group' || o.type === 'editgroup') && o.id === groupId) || null;
}
function getGroupMembers(groupId) {
  const g = getGroup(groupId);
  return g ? g.memberIds.map(id => getObj(id)).filter(Boolean) : [];
}

function getDefiningPointIds(obj) {
  switch (obj.type) {
    case 'segment': case 'vector': case 'line': case 'ray':
    case 'perp-bisector':
      return [obj.p1id, obj.p2id].filter(Boolean);
    case 'angle-bisector':
      return [obj.p1id, obj.p2id, obj.p3id].filter(Boolean);
    case 'parallel': case 'perpendicular':
      return [obj.pointId].filter(Boolean);
    case 'circle':
      return [obj.centerId, obj.radiusPointId].filter(Boolean);
    case 'circle3pts':
      return [obj.p1id, obj.p2id, obj.p3id].filter(Boolean);
    case 'semicircle':
      return [obj.p1id, obj.p2id].filter(Boolean);
    case 'arc':
      return [obj.p1id, obj.p2id, obj.p3id].filter(Boolean);
    case 'polygon': case 'rect':
      return obj.pointIds ? [...obj.pointIds] : [];
    case 'angle-measure': case 'distance-measure':
      return [obj.p1id, obj.p2id, obj.p3id].filter(Boolean);
    default:
      return [];
  }
}

function moveObjectBy(obj, ddx, ddy, movedSet, ignoreFixed = false) {
  if (!movedSet) movedSet = new Set();
  if (obj.type === 'point') {
    if ((ignoreFixed || !obj.fixed) && !movedSet.has(obj.id)) { movedSet.add(obj.id); obj.x += ddx; obj.y += ddy; }
    return;
  }
  if (obj.type === 'text') { obj.x += ddx; obj.y += ddy; return; }
  getDefiningPointIds(obj).forEach(id => {
    if (movedSet.has(id)) return; movedSet.add(id);
    const pt = getObj(id);
    if (pt && pt.type === 'point' && (ignoreFixed || !pt.fixed)) { pt.x += ddx; pt.y += ddy; }
  });
}

function isLineLike(obj) {
  return ['line', 'segment', 'ray', 'vector', 'parallel', 'perpendicular', 'perp-bisector', 'angle-bisector'].includes(obj?.type);
}

function isCircleLike(obj) {
  return ['circle', 'circle3pts', 'semicircle', 'arc'].includes(obj?.type);
}

// ── Object factory helpers ────────────────────────
function makePoint(wx, wy, label, color = '#7c9eff') {
  const obj = { id: uid(), type: 'point', label: label || nextPointLabel(), color, lineWidth: 2, visible: true, x: wx, y: wy, fixed: false };
  push(obj); return obj;
}

function snapToGrid(wx, wy) {
  if (!state.showGrid) return { x: wx, y: wy };
  // Use explicit snapUnit if set (from editor), else auto from zoom level
  const snap = (state.snapUnit != null) ? state.snapUnit
             : (state.scale < 30 ? 2 : state.scale < 80 ? 1 : 0.5);
  if (snap <= 0) return { x: wx, y: wy };
  return { x: Math.round(wx / snap) * snap, y: Math.round(wy / snap) * snap };
}

function push(obj) {
  state.objects.push(obj);
  saveUndo();
  updateAlgebra();
}

function pushBatch(objs) {
  objs.forEach(o => state.objects.push(o));
  saveUndo();
  updateAlgebra();
}

// ── Undo / Redo ───────────────────────────────────
function saveUndo() {
  state.undoStack.push(JSON.stringify(state.objects));
  if (state.undoStack.length > 60) state.undoStack.shift();
  state.redoStack = [];
  updateUndoButtons();
}

function undo() {
  if (state.undoStack.length < 2) return;
  state.redoStack.push(state.undoStack.pop());
  restoreObjects(JSON.parse(state.undoStack[state.undoStack.length - 1]));
  updateUndoButtons();
  updateAlgebra();
  render();
}

function redo() {
  if (!state.redoStack.length) return;
  const s = state.redoStack.pop();
  state.undoStack.push(s);
  restoreObjects(JSON.parse(s));
  updateUndoButtons();
  updateAlgebra();
  render();
}

function restoreObjects(objs) {
  state.objects.length = 0;
  objs.forEach(o => state.objects.push(o));
  nextId = state.objects.reduce((m, o) => Math.max(m, o.id), 0) + 1;
}

function updateUndoButtons() {
  document.getElementById('btn-undo').disabled = state.undoStack.length < 2;
  document.getElementById('btn-redo').disabled = state.redoStack.length === 0;
}

// ── Color palette (cycling) ───────────────────────
const COLORS = ['#7c9eff', '#f38ba8', '#a6e3a1', '#f9e2af', '#cba6f7', '#89dceb', '#fab387'];
let colorIdx = 0;
function nextColor() { return COLORS[colorIdx++ % COLORS.length]; }

// ══════════════════════════════════════════════════════
// RENDERING
// ══════════════════════════════════════════════════════

// ── Zone system ───────────────────────────────────
function buildZoneLayout(activeZoneIds, zoneW, zoneH, gap) {
  zoneW = zoneW || 8; zoneH = zoneH || 6; gap = gap || 0.5;
  const defs = {
    'zone-top':    { label: 'Dessus',  dx: 0,            dy: zoneH + gap  },
    'zone-center': { label: 'Face',    dx: 0,            dy: 0            },
    'zone-left':   { label: 'Gauche',  dx: -(zoneW+gap), dy: 0            },
    'zone-right':  { label: 'Droite',  dx: zoneW + gap,  dy: 0            },
    'zone-bottom': { label: 'Dessous', dx: 0,            dy: -(zoneH+gap) },
  };
  return activeZoneIds.map(id => {
    const d = defs[id]; if (!d) return null;
    return {
      id, label: d.label,
      x1: d.dx - zoneW/2, y1: d.dy - zoneH/2,
      x2: d.dx + zoneW/2, y2: d.dy + zoneH/2,
      state: 'active'
    };
  }).filter(Boolean);
}

const ZONE_COLORS = {
  neutral: { fill: 'rgba(100,100,150,0.08)', stroke: 'rgba(100,100,150,0.35)' },
  active:  { fill: 'rgba(100,150,255,0.10)', stroke: 'rgba(100,150,255,0.50)' },
  yellow:  { fill: 'rgba(250,200,50,0.20)',  stroke: 'rgba(250,200,50,0.85)'  },
  green:   { fill: 'rgba(50,210,100,0.22)',  stroke: 'rgba(50,210,100,0.90)'  },
  error:   { fill: 'rgba(240,80,80,0.18)',   stroke: 'rgba(240,80,80,0.80)'   },
};

function drawZones() {
  if (!state.zonesVisible || !state.zones.length) return;
  state.zones.forEach(z => {
    const c = ZONE_COLORS[z.state] || ZONE_COLORS.active;
    const p1 = worldToCanvas(z.x1, z.y2);
    const p2 = worldToCanvas(z.x2, z.y1);
    const w = p2.x - p1.x, h = p2.y - p1.y;
    ctx.save();
    ctx.fillStyle = c.fill;
    ctx.strokeStyle = c.stroke;
    ctx.lineWidth = 2;
    ctx.setLineDash([6, 3]);
    ctx.fillRect(p1.x, p1.y, w, h);
    ctx.strokeRect(p1.x, p1.y, w, h);
    ctx.setLineDash([]);
    // Label
    const cx = (p1.x + p2.x) / 2, cy = (p1.y + p2.y) / 2;
    ctx.fillStyle = c.stroke;
    ctx.font = `bold ${Math.max(10, Math.min(16, state.scale * 0.25))}px sans-serif`;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(z.label, cx, cy);
    ctx.restore();
  });

  // Draw palette area label if there are figure groups
  if (state.figureGroups.length > 0) {
    const palette = getPaletteArea();
    const p1 = worldToCanvas(palette.x1, palette.y2);
    const p2 = worldToCanvas(palette.x2, palette.y1);
    ctx.save();
    ctx.strokeStyle = 'rgba(180,180,255,0.3)';
    ctx.fillStyle = 'rgba(100,100,200,0.06)';
    ctx.lineWidth = 1.5;
    ctx.setLineDash([4, 4]);
    ctx.fillRect(p1.x, p1.y, p2.x - p1.x, p2.y - p1.y);
    ctx.strokeRect(p1.x, p1.y, p2.x - p1.x, p2.y - p1.y);
    ctx.setLineDash([]);
    ctx.fillStyle = 'rgba(180,180,255,0.5)';
    ctx.font = `bold ${Math.max(9, Math.min(13, state.scale * 0.2))}px sans-serif`;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('PIÈCES', (p1.x + p2.x) / 2, p1.y - 10);
    ctx.restore();
  }
}

function drawFigureGroupPivots() {
  state.figureGroups.forEach(fg => {
    const pivot = state.objects.find(o => o.id === fg.pivotId || o.label === fg.pivotLabel);
    if (!pivot || pivot.x == null) return;
    const c = worldToCanvas(pivot.x, pivot.y);
    ctx.save();
    ctx.strokeStyle = '#89b4fa';
    ctx.fillStyle = 'rgba(137,180,250,0.25)';
    ctx.lineWidth = 2.5;
    ctx.beginPath(); ctx.arc(c.x, c.y, 10, 0, Math.PI*2); ctx.fill(); ctx.stroke();
    // + symbol
    ctx.strokeStyle = '#89b4fa'; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(c.x-5, c.y); ctx.lineTo(c.x+5, c.y); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(c.x, c.y-5); ctx.lineTo(c.x, c.y+5); ctx.stroke();
    // Label
    if (fg.label) {
      ctx.fillStyle = '#89b4fa';
      ctx.font = '10px sans-serif'; ctx.textAlign = 'left'; ctx.textBaseline = 'top';
      ctx.fillText(fg.label, c.x + 12, c.y - 6);
    }
    ctx.restore();
  });
}

function getGroupZoneAt(x, y) {
  return state.zones.find(z => x >= z.x1 && x <= z.x2 && y >= z.y1 && y <= z.y2) || null;
}

// Returns bounding box {minX,maxX,minY,maxY} of all defining points of a figureGroup
function getGroupBounds(fg) {
  let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
  fg.objectIds.forEach(oid => {
    const o = state.objects.find(ob => ob.id === oid);
    if (!o) return;
    const ptIds = getDefiningPointIds(o);
    const pts = ptIds.length > 0 ? ptIds.map(pid => getObj(pid)).filter(Boolean) : (isPointLike(o) ? [o] : []);
    pts.forEach(pt => {
      if (pt.x < minX) minX = pt.x; if (pt.x > maxX) maxX = pt.x;
      if (pt.y < minY) minY = pt.y; if (pt.y > maxY) maxY = pt.y;
    });
  });
  return { minX, maxX, minY, maxY };
}

function getPaletteArea() {
  // Area above all zones where figures start
  const topY = state.zones.reduce((m, z) => Math.max(m, z.y2), 6) + 1.5;
  const totalW = state.figureGroups.length * 5;
  return { x1: -totalW / 2, y1: topY, x2: totalW / 2, y2: topY + 5 };
}

function computeGroupStartPos(groupIndex) {
  const topY = state.zones.reduce((m, z) => Math.max(m, z.y2), 6) + 2.5;
  const spacing = 5;
  const n = Math.max(1, state.figureGroups.length + 1);
  const x = -(n - 1) * spacing / 2 + groupIndex * spacing;
  return { x, y: topY };
}

function render() {
  evalAll();
  const W = canvas.width, H = canvas.height;
  ctx.clearRect(0, 0, W, H);

  // Background
  ctx.fillStyle = '#0f0f1a';
  ctx.fillRect(0, 0, W, H);

  if (state.showGrid) drawGrid();
  if (state.showAxes) drawAxes();
  drawZones();

  // Draw objects (back to front)
  // First: filled shapes (sorted by zIndex)
  const fillables = state.objects.filter(o => o.visible && (o.type === 'polygon' || o.type === 'rect'));
  fillables.sort((a, b) => (a.zIndex || 0) - (b.zIndex || 0));
  fillables.forEach(o => { if (o.type === 'rect') drawRect(o, true); else drawPolygon(o, true); });
  // Then: all others
  state.objects.forEach(o => {
    if (!o.visible) return;
    switch (o.type) {
      case 'point': case 'midpoint': case 'reflect-line': case 'reflect-point':
      case 'rotate': case 'translate': case 'intersect': drawPoint(o); break;
      case 'segment': drawSegment(o); break;
      case 'line': drawLine(o); break;
      case 'ray': drawRay(o); break;
      case 'vector': drawVector(o); break;
      case 'parallel': case 'perpendicular': case 'perp-bisector': case 'angle-bisector': drawDerivedLine(o); break;
      case 'circle': drawCircle(o); break;
      case 'circle3pts': drawCircle3pts(o); break;
      case 'semicircle': drawSemicircle(o); break;
      case 'arc': drawArc(o); break;
      case 'polygon': drawPolygon(o, false); break;
      case 'rect': drawRect(o, false); break;
      case 'text': drawText(o); break;
      case 'angle-measure': drawAngleMeasure(o); break;
      case 'distance-measure': drawDistanceMeasure(o); break;
      case 'area-measure': break; // shown in algebra
    }
  });

  // Draw group selection overlays
  if (state.selected.length === 1) {
    const selObj = getObj(state.selected[0]);
    if (selObj && selObj.type === 'group') {
      const members = getGroupMembers(selObj.id);
      ctx.save();
      members.forEach(m => {
        if (isPointLike(m) && m.x != null) {
          const c = worldToCanvas(m.x, m.y);
          ctx.beginPath();
          ctx.arc(c.x, c.y, 12, 0, Math.PI * 2);
          ctx.strokeStyle = 'rgba(255,180,50,0.6)';
          ctx.lineWidth = 2;
          ctx.stroke();
          ctx.beginPath();
          ctx.arc(c.x, c.y, 12, 0, Math.PI * 2);
          ctx.fillStyle = 'rgba(255,180,50,0.08)';
          ctx.fill();
        }
      });
      ctx.restore();
    }
  }
  // Draw group editing mode indicator
  if (state.editingGroupId) {
    const members = getGroupMembers(state.editingGroupId);
    ctx.save();
    members.forEach(m => {
      if (isPointLike(m) && m.x != null) {
        const c = worldToCanvas(m.x, m.y);
        ctx.beginPath();
        ctx.arc(c.x, c.y, 14, 0, Math.PI * 2);
        ctx.strokeStyle = 'rgba(100,200,255,0.5)';
        ctx.lineWidth = 1.5;
        ctx.setLineDash([4, 3]);
        ctx.stroke();
        ctx.setLineDash([]);
      }
    });
    ctx.restore();
  }

  drawTempPreview();
  drawFigureGroupPivots();

  // Draw lasso selection rectangle
  if (state.isLasso && state.lassoStart && state.lassoEnd) {
    const x = Math.min(state.lassoStart.cx, state.lassoEnd.cx);
    const y = Math.min(state.lassoStart.cy, state.lassoEnd.cy);
    const w = Math.abs(state.lassoEnd.cx - state.lassoStart.cx);
    const h = Math.abs(state.lassoEnd.cy - state.lassoStart.cy);
    ctx.save();
    ctx.strokeStyle = '#89b4fa';
    ctx.fillStyle = 'rgba(137,180,250,0.08)';
    ctx.lineWidth = 1.5;
    ctx.setLineDash([5, 3]);
    ctx.strokeRect(x, y, w, h);
    ctx.fillRect(x, y, w, h);
    ctx.restore();
  }
}

function drawGrid() {
  const W = canvas.width, H = canvas.height;
  const minW = canvasToWorld(0, 0), maxW = canvasToWorld(W, H);
  const gridStep = pickGridStep();

  ctx.strokeStyle = 'rgba(255,255,255,0.05)';
  ctx.lineWidth = 1;

  const startX = Math.ceil(minW.x / gridStep) * gridStep;
  for (let x = startX; x <= maxW.x + gridStep; x += gridStep) {
    const c = worldToCanvas(x, 0);
    ctx.beginPath(); ctx.moveTo(c.x, 0); ctx.lineTo(c.x, H); ctx.stroke();
  }
  const startY = Math.ceil(maxW.y / gridStep) * gridStep;
  for (let y = startY; y <= minW.y + gridStep; y += gridStep) {
    const c = worldToCanvas(0, y);
    ctx.beginPath(); ctx.moveTo(0, c.y); ctx.lineTo(W, c.y); ctx.stroke();
  }
}

function pickGridStep() {
  const unitPx = state.scale;
  if (unitPx >= 120) return 0.5;
  if (unitPx >= 40) return 1;
  if (unitPx >= 20) return 2;
  if (unitPx >= 10) return 5;
  return 10;
}

function drawAxes() {
  const W = canvas.width, H = canvas.height;
  const o = worldToCanvas(0, 0);

  ctx.strokeStyle = 'rgba(255,255,255,0.18)';
  ctx.lineWidth = 1;

  // X axis
  ctx.beginPath(); ctx.moveTo(0, o.y); ctx.lineTo(W, o.y); ctx.stroke();
  // Y axis
  ctx.beginPath(); ctx.moveTo(o.x, 0); ctx.lineTo(o.x, H); ctx.stroke();

  // Axis labels
  ctx.fillStyle = 'rgba(255,255,255,0.3)';
  ctx.font = '11px monospace';
  ctx.textAlign = 'left'; ctx.textBaseline = 'top';
  ctx.fillText('x', W - 16, o.y + 4);
  ctx.textAlign = 'right'; ctx.textBaseline = 'alphabetic';
  ctx.fillText('y', o.x - 4, 14);

  // Tick marks + numbers
  const step = pickGridStep();
  const minW = canvasToWorld(0, H), maxW = canvasToWorld(W, 0);

  ctx.fillStyle = 'rgba(255,255,255,0.25)';
  ctx.font = '9px monospace';
  ctx.textAlign = 'center';

  const startX = Math.ceil(minW.x / step) * step;
  for (let x = startX; x <= maxW.x; x += step) {
    if (Math.abs(x) < step * 0.1) continue;
    const c = worldToCanvas(x, 0);
    ctx.beginPath(); ctx.moveTo(c.x, o.y - 3); ctx.lineTo(c.x, o.y + 3); ctx.stroke();
    if (state.scale > 25) ctx.fillText(formatNum(x), c.x, o.y + 5);
  }

  ctx.textAlign = 'right';
  const startY = Math.ceil(maxW.y / step) * step;
  for (let y = startY; y <= minW.y; y += step) {
    if (Math.abs(y) < step * 0.1) continue;
    const c = worldToCanvas(0, y);
    ctx.beginPath(); ctx.moveTo(o.x - 3, c.y); ctx.lineTo(o.x + 3, c.y); ctx.stroke();
    if (state.scale > 25) ctx.fillText(formatNum(y), o.x - 5, c.y + 3);
  }
}

function formatNum(n) {
  if (Number.isInteger(n)) return String(n);
  return n.toFixed(1).replace(/\.0$/, '');
}

function isSelected(obj) { return state.selected.includes(obj.id); }
function isHovered(obj) { return state.hover === obj.id; }

function objStroke(obj, alpha = 1) {
  const sel = isSelected(obj), hov = isHovered(obj);
  if (sel) return `rgba(255,220,100,${alpha})`;
  if (hov) return adjustAlpha(obj.color || '#7c9eff', alpha * 1.4);
  return adjustAlpha(obj.color || '#7c9eff', alpha);
}

// Apply stroke style + dashed pattern to ctx before drawing a line object
function applyLineStyle(obj) {
  ctx.strokeStyle = objStroke(obj);
  ctx.lineWidth = isSelected(obj) ? 3.5 : (obj.lineWidth || 2);
  if (obj.dashed) {
    const dash = obj.lineWidth > 3 ? [8, 6] : [6, 4];
    ctx.setLineDash(dash);
  } else {
    ctx.setLineDash([]);
  }
}
function resetLineDash() { ctx.setLineDash([]); }

function adjustAlpha(hex, alpha) {
  // hex may be rgb() or #rrggbb
  if (hex.startsWith('#')) {
    const r = parseInt(hex.slice(1, 3), 16);
    const g = parseInt(hex.slice(3, 5), 16);
    const b = parseInt(hex.slice(5, 7), 16);
    return `rgba(${r},${g},${b},${Math.min(1, alpha)})`;
  }
  return hex;
}

function drawPoint(obj) {
  const c = worldToCanvas(obj.x, obj.y);
  const sel = isSelected(obj), hov = isHovered(obj);
  const r = sel || hov ? 6 : 5;

  if (sel) {
    // Halo extérieur jaune
    ctx.beginPath(); ctx.arc(c.x, c.y, r + 9, 0, Math.PI * 2);
    ctx.fillStyle = 'rgba(255,220,50,0.22)'; ctx.fill();
    // Anneau jaune épais
    ctx.beginPath(); ctx.arc(c.x, c.y, r + 4, 0, Math.PI * 2);
    ctx.strokeStyle = 'rgba(255,220,50,1)'; ctx.lineWidth = 3; ctx.stroke();
  }

  // Group membership highlight
  if (!sel && obj.groupId) {
    const grpSelected = state.selected.length === 1 && state.selected[0] === obj.groupId;
    if (grpSelected) {
      ctx.beginPath(); ctx.arc(c.x, c.y, r + 5, 0, Math.PI * 2);
      ctx.strokeStyle = 'rgba(255,180,50,0.5)'; ctx.lineWidth = 1.5; ctx.stroke();
    }
  }

  ctx.beginPath(); ctx.arc(c.x, c.y, r, 0, Math.PI * 2);
  ctx.fillStyle = sel ? 'rgba(255,220,50,1)' : objStroke(obj);
  ctx.fill();

  ctx.beginPath(); ctx.arc(c.x, c.y, r - 2, 0, Math.PI * 2);
  ctx.fillStyle = 'rgba(0,0,0,0.4)';
  ctx.fill();

  // Label
  ctx.fillStyle = sel ? 'rgba(255,220,50,1)' : objStroke(obj);
  ctx.font = 'bold 12px serif';
  ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
  ctx.fillText(obj.label, c.x + 7, c.y - 4);
}

function drawSegment(obj) {
  const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
  if (!p1 || !p2) return;
  const c1 = worldToCanvas(p1.x, p1.y), c2 = worldToCanvas(p2.x, p2.y);
  ctx.beginPath(); ctx.moveTo(c1.x, c1.y); ctx.lineTo(c2.x, c2.y);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
}

function drawLine(obj) {
  const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
  if (!p1 || !p2) return;
  extendAndDraw(p1, p2, obj, false, false);
}

function drawRay(obj) {
  const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
  if (!p1 || !p2) return;
  extendAndDraw(p1, p2, obj, false, true);
}

function extendAndDraw(p1w, p2w, obj, clampStart, clampEnd) {
  const W = canvas.width, H = canvas.height;
  const c1 = worldToCanvas(p1w.x, p1w.y);
  const c2 = worldToCanvas(p2w.x, p2w.y);
  const dx = c2.x - c1.x, dy = c2.y - c1.y;
  let tMin = -1000, tMax = 1000;

  if (!clampStart && !clampEnd) {
    // Infinite line: clip to canvas
    if (Math.abs(dx) > 0.001) {
      tMin = Math.max(tMin, -c1.x / dx);
      tMax = Math.min(tMax, (W - c1.x) / dx);
      if (dx < 0) [tMin, tMax] = [tMax, tMin];
    }
    if (Math.abs(dy) > 0.001) {
      const t1 = -c1.y / dy, t2 = (H - c1.y) / dy;
      tMin = Math.max(tMin, Math.min(t1, t2));
      tMax = Math.min(tMax, Math.max(t1, t2));
    }
  } else if (clampEnd) {
    // Ray: start at p1, extend
    tMin = 0; tMax = 2000;
  }

  ctx.beginPath();
  ctx.moveTo(c1.x + tMin * dx, c1.y + tMin * dy);
  ctx.lineTo(c1.x + tMax * dx, c1.y + tMax * dy);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
}

function drawDerivedLine(obj) {
  if (obj.px == null) return;
  const W = canvas.width, H = canvas.height;
  const c = worldToCanvas(obj.px, obj.py);
  const dx = obj.dx * state.scale, dy = -obj.dy * state.scale;

  let tMin = -1000, tMax = 1000;
  if (Math.abs(dx) > 0.001) {
    tMin = Math.max(tMin, -c.x / dx);
    tMax = Math.min(tMax, (W - c.x) / dx);
    if (dx < 0) [tMin, tMax] = [tMax, tMin];
  }
  if (Math.abs(dy) > 0.001) {
    const t1 = -c.y / dy, t2 = (H - c.y) / dy;
    tMin = Math.max(tMin, Math.min(t1, t2));
    tMax = Math.min(tMax, Math.max(t1, t2));
  }

  ctx.beginPath();
  ctx.moveTo(c.x + tMin * dx, c.y + tMin * dy);
  ctx.lineTo(c.x + tMax * dx, c.y + tMax * dy);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
}

function drawVector(obj) {
  const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
  if (!p1 || !p2) return;
  const c1 = worldToCanvas(p1.x, p1.y), c2 = worldToCanvas(p2.x, p2.y);
  ctx.beginPath(); ctx.moveTo(c1.x, c1.y); ctx.lineTo(c2.x, c2.y);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
  // Arrow head
  const angle = Math.atan2(c2.y - c1.y, c2.x - c1.x);
  const size = 12;
  ctx.beginPath();
  ctx.moveTo(c2.x, c2.y);
  ctx.lineTo(c2.x - size * Math.cos(angle - 0.4), c2.y - size * Math.sin(angle - 0.4));
  ctx.lineTo(c2.x - size * Math.cos(angle + 0.4), c2.y - size * Math.sin(angle + 0.4));
  ctx.closePath();
  ctx.fillStyle = objStroke(obj); ctx.fill();
}

function drawCircle(obj) {
  const cen = getPoint(obj.centerId);
  if (!cen || !obj.r) return;
  const cc = worldToCanvas(cen.x, cen.y);
  const rPx = obj.r * state.scale;
  ctx.beginPath(); ctx.arc(cc.x, cc.y, rPx, 0, Math.PI * 2);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
  if (isSelected(obj)) {
    ctx.beginPath(); ctx.arc(cc.x, cc.y, rPx, 0, Math.PI * 2);
    ctx.fillStyle = adjustAlpha(obj.color || '#7c9eff', 0.05); ctx.fill();
  }
}

function drawCircle3pts(obj) {
  if (obj.cx == null) return;
  const cc = worldToCanvas(obj.cx, obj.cy);
  const rPx = obj.r * state.scale;
  ctx.beginPath(); ctx.arc(cc.x, cc.y, rPx, 0, Math.PI * 2);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
}

function drawSemicircle(obj) {
  const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
  if (!p1 || !p2) return;
  const cx = (p1.x + p2.x) / 2, cy = (p1.y + p2.y) / 2;
  const r = dist(p1, p2) / 2;
  const cc = worldToCanvas(cx, cy);
  const rPx = r * state.scale;
  const angle = Math.atan2(-(p2.y - p1.y), p2.x - p1.x);
  ctx.beginPath(); ctx.arc(cc.x, cc.y, rPx, angle, angle + Math.PI);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
  const c1 = worldToCanvas(p1.x, p1.y), c2 = worldToCanvas(p2.x, p2.y);
  ctx.beginPath(); ctx.moveTo(c1.x, c1.y); ctx.lineTo(c2.x, c2.y);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
}

function drawArc(obj) {
  const center = getPoint(obj.centerId);
  if (!center || obj.r == null) return;
  const cc = worldToCanvas(center.x, center.y);
  const rPx = obj.r * state.scale;
  const a1 = obj.startAngle || 0;
  const a2 = obj.endAngle || Math.PI;
  ctx.beginPath(); ctx.arc(cc.x, cc.y, rPx, a1, a2);
  applyLineStyle(obj); ctx.stroke(); resetLineDash();
}

function drawRect(obj, fillOnly) {
  const pts = obj.pointIds.map(getPoint).filter(Boolean);
  if (pts.length < 4) return;
  ctx.beginPath();
  const c0 = worldToCanvas(pts[0].x, pts[0].y);
  ctx.moveTo(c0.x, c0.y);
  for (let i = 1; i < 4; i++) { const c = worldToCanvas(pts[i].x, pts[i].y); ctx.lineTo(c.x, c.y); }
  ctx.closePath();
  if (fillOnly) {
    const alpha = obj.fillOpacity != null ? obj.fillOpacity : 0.15;
    ctx.fillStyle = adjustAlpha(obj.fillColor || obj.color || '#7c9eff', alpha);
    ctx.fill();
  } else {
    applyLineStyle(obj); ctx.stroke(); resetLineDash();
  }
}

function drawPolygon(obj, fillOnly) {
  const pts = obj.pointIds.map(getPoint).filter(Boolean);
  if (pts.length < 2) return;
  ctx.beginPath();
  const c0 = worldToCanvas(pts[0].x, pts[0].y);
  ctx.moveTo(c0.x, c0.y);
  for (let i = 1; i < pts.length; i++) {
    const c = worldToCanvas(pts[i].x, pts[i].y);
    ctx.lineTo(c.x, c.y);
  }
  ctx.closePath();
  if (fillOnly) {
    ctx.fillStyle = adjustAlpha(obj.color || '#7c9eff', 0.12);
    ctx.fill();
  } else {
    applyLineStyle(obj); ctx.stroke(); resetLineDash();
  }
}

function drawText(obj) {
  const c = worldToCanvas(obj.x, obj.y);
  ctx.fillStyle = obj.color || '#cdd6f4';
  ctx.font = `${obj.fontSize || 14}px serif`;
  ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic';
  ctx.fillText(obj.text, c.x, c.y);
}

function drawAngleMeasure(obj) {
  const v = getPoint(obj.vertexId), a = getPoint(obj.p1id), b = getPoint(obj.p2id);
  if (!v || !a || !b) return;
  const cv = worldToCanvas(v.x, v.y);
  const d1 = dist(v, a) || 1, d2 = dist(v, b) || 1;
  const ang1 = Math.atan2(-(a.y - v.y), a.x - v.x);
  const ang2 = Math.atan2(-(b.y - v.y), b.x - v.x);
  const arcR = Math.min(30, 1.5 * state.scale);

  ctx.beginPath();
  ctx.arc(cv.x, cv.y, arcR, ang1, ang2, false);
  ctx.strokeStyle = adjustAlpha(obj.color || '#f9e2af', 0.9);
  ctx.lineWidth = 1.5; ctx.stroke();

  ctx.fillStyle = adjustAlpha(obj.color || '#f9e2af', 0.2);
  ctx.beginPath(); ctx.moveTo(cv.x, cv.y);
  ctx.arc(cv.x, cv.y, arcR, ang1, ang2, false);
  ctx.closePath(); ctx.fill();

  if (obj.value != null) {
    const midAng = (ang1 + ang2) / 2;
    const lx = cv.x + (arcR + 16) * Math.cos(midAng);
    const ly = cv.y + (arcR + 16) * Math.sin(midAng);
    ctx.fillStyle = obj.color || '#f9e2af';
    ctx.font = '11px monospace'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(obj.value.toFixed(1) + '°', lx, ly);
  }
}

function drawDistanceMeasure(obj) {
  const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
  if (!p1 || !p2) return;
  const c1 = worldToCanvas(p1.x, p1.y), c2 = worldToCanvas(p2.x, p2.y);
  const mx = (c1.x + c2.x) / 2, my = (c1.y + c2.y) / 2;
  const angle = Math.atan2(c2.y - c1.y, c2.x - c1.x);
  const offset = 18;
  const tx = mx + offset * Math.sin(angle);
  const ty = my - offset * Math.cos(angle);

  ctx.fillStyle = obj.color || '#89dceb';
  ctx.font = '11px monospace'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  if (obj.value != null) ctx.fillText(obj.value.toFixed(2), tx, ty);
}

// ── Temp preview ──────────────────────────────────
function drawTempPreview() {
  const pts = state.tempPoints;
  if (!pts.length) return;

  // Draw already-placed temp points
  pts.forEach(p => {
    const c = worldToCanvas(p.x, p.y);
    ctx.beginPath(); ctx.arc(c.x, c.y, 4, 0, Math.PI * 2);
    ctx.fillStyle = 'rgba(255,220,100,0.8)'; ctx.fill();
  });

  // Preview line to mouse
  if (state.mouseWorld && pts.length >= 1) {
    const last = pts[pts.length - 1];
    const c1 = worldToCanvas(last.x, last.y);
    const c2 = worldToCanvas(state.mouseWorld.x, state.mouseWorld.y);
    ctx.beginPath(); ctx.moveTo(c1.x, c1.y); ctx.lineTo(c2.x, c2.y);
    ctx.strokeStyle = 'rgba(255,220,100,0.5)';
    ctx.lineWidth = 1.5; ctx.setLineDash([5, 4]); ctx.stroke(); ctx.setLineDash([]);
  }

  if (state.tool === 'polygon' && state.mouseWorld && pts.length >= 2) {
    const first = pts[0];
    const c2 = worldToCanvas(first.x, first.y);
    const cm = worldToCanvas(state.mouseWorld.x, state.mouseWorld.y);
    ctx.beginPath(); ctx.moveTo(cm.x, cm.y); ctx.lineTo(c2.x, c2.y);
    ctx.strokeStyle = 'rgba(255,220,100,0.3)';
    ctx.lineWidth = 1; ctx.setLineDash([3, 3]); ctx.stroke(); ctx.setLineDash([]);
  }

  if (state.tool === 'rectangle' && pts.length === 1 && state.mouseWorld) {
    const a = pts[0], m = state.mouseWorld;
    const corners = [worldToCanvas(a.x, a.y), worldToCanvas(m.x, a.y), worldToCanvas(m.x, m.y), worldToCanvas(a.x, m.y)];
    ctx.beginPath();
    ctx.moveTo(corners[0].x, corners[0].y);
    corners.slice(1).forEach(c => ctx.lineTo(c.x, c.y));
    ctx.closePath();
    ctx.fillStyle = 'rgba(124,158,255,0.10)'; ctx.fill();
    ctx.strokeStyle = 'rgba(255,220,100,0.6)'; ctx.lineWidth = 1.5; ctx.setLineDash([5,3]); ctx.stroke(); ctx.setLineDash([]);
  }

  if ((state.tool === 'circle-center-point' || state.tool === 'semicircle') && pts.length === 1 && state.mouseWorld) {
    const center = pts[0];
    const r = dist(center, state.mouseWorld);
    const cc = worldToCanvas(center.x, center.y);
    const rPx = r * state.scale;
    if (state.tool === 'circle-center-point') {
      ctx.beginPath(); ctx.arc(cc.x, cc.y, rPx, 0, Math.PI * 2);
    } else {
      const angle = Math.atan2(-(state.mouseWorld.y - center.y), state.mouseWorld.x - center.x);
      ctx.beginPath(); ctx.arc(cc.x, cc.y, rPx, angle, angle + Math.PI);
    }
    ctx.strokeStyle = 'rgba(255,220,100,0.5)'; ctx.lineWidth = 1.5; ctx.stroke();
  }
}

// ══════════════════════════════════════════════════════
// TOOL HANDLERS (click actions)
// ══════════════════════════════════════════════════════

const toolHandlers = {
  point(wx, wy) {
    const snapped = snapToGrid(wx, wy);
    makePoint(snapped.x, snapped.y);
    render();
  },
  'point-on-object'(wx, wy) {
    // Snap to nearest line/circle object
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (obj && (isLineLike(obj) || isCircleLike(obj))) {
      const snapped = snapToObjectPoint(obj, wx, wy);
      makePoint(snapped.x, snapped.y);
    } else {
      const snapped = snapToGrid(wx, wy);
      makePoint(snapped.x, snapped.y);
    }
    render();
  },
  midpoint(wx, wy) {
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (!obj) { setStatus('Cliquez sur un segment ou deux points'); return; }
    if (obj.type === 'segment' || obj.type === 'vector') {
      const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
      if (!p1 || !p2) return;
      const mid = { id: uid(), type: 'midpoint', label: nextPointLabel(), color: '#cba6f7', lineWidth: 2, visible: true, x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2, p1id: obj.p1id, p2id: obj.p2id };
      push(mid); render();
    } else if (isPointLike(obj)) {
      state.tempPoints.push({ x: obj.x, y: obj.y, id: obj.id });
      if (state.tempPoints.length === 2) {
        const [a, b] = state.tempPoints;
        const mid = { id: uid(), type: 'midpoint', label: nextPointLabel(), color: '#cba6f7', lineWidth: 2, visible: true, x: (a.x + b.x) / 2, y: (a.y + b.y) / 2, p1id: a.id, p2id: b.id };
        push(mid); state.tempPoints = []; render();
      } else { setStatus('Cliquez sur le deuxième point'); }
    }
  },
  intersect(wx, wy) {
    const raw = state.rawClickWorld || { x: wx, y: wy };
    const obj = objectAtCanvas(...worldToCanvasPx(raw.x, raw.y));
    if (!obj || (!isLineLike(obj) && !isCircleLike(obj))) { setStatus('Cliquez sur une droite ou un cercle'); return; }
    state.tempPoints.push({ ref: obj.id });
    if (state.tempPoints.length === 2) {
      const l1 = getObj(state.tempPoints[0].ref), l2 = getObj(state.tempPoints[1].ref);
      const ip = computeIntersect(l1, l2);
      if (ip) {
        const pt = { id: uid(), type: 'intersect', label: nextPointLabel(), color: '#f9e2af', lineWidth: 2, visible: true, x: ip.x, y: ip.y, l1id: l1.id, l2id: l2.id };
        push(pt);
      } else { setStatus('Ces objets ne se croisent pas'); }
      state.tempPoints = []; render();
    } else { setStatus('Cliquez sur le deuxième objet'); }
  },
  segment: twoPointTool('segment'),
  line: twoPointTool('line'),
  ray: twoPointTool('ray'),
  vector: twoPointTool('vector'),

  parallel(wx, wy) {
    const raw = state.rawClickWorld || { x: wx, y: wy };
    const obj = objectAtCanvas(...worldToCanvasPx(raw.x, raw.y));
    if (!state.tempPoints.length) {
      if (obj && isLineLike(obj)) {
        state.tempPoints.push({ lineId: obj.id });
        setStatus('Cliquez sur le point de passage (ou dans l\'espace vide pour en créer un)');
      } else if (obj && isPointLike(obj)) {
        state.tempPoints.push({ pointId: obj.id });
        setStatus('Cliquez sur la droite de référence');
      } else { setStatus('Cliquez d\'abord sur une droite ou un segment'); }
    } else {
      const prev = state.tempPoints[0];
      if (prev.lineId) {
        const pt = (obj && isPointLike(obj)) ? obj : makePoint(wx, wy);
        const par = { id: uid(), type: 'parallel', label: nextLineLabel(), color: nextColor(), lineWidth: 2, visible: true, refLineId: prev.lineId, pointId: pt.id, px: 0, py: 0, dx: 1, dy: 0 };
        push(par); state.tempPoints = []; render();
      } else if (prev.pointId && obj && isLineLike(obj)) {
        const par = { id: uid(), type: 'parallel', label: nextLineLabel(), color: nextColor(), lineWidth: 2, visible: true, refLineId: obj.id, pointId: prev.pointId, px: 0, py: 0, dx: 1, dy: 0 };
        push(par); state.tempPoints = []; render();
      } else { setStatus('Cliquez sur la droite de référence'); }
    }
  },

  perpendicular(wx, wy) {
    const raw = state.rawClickWorld || { x: wx, y: wy };
    const obj = objectAtCanvas(...worldToCanvasPx(raw.x, raw.y));
    if (!state.tempPoints.length) {
      if (obj && isLineLike(obj)) {
        state.tempPoints.push({ lineId: obj.id });
        setStatus('Cliquez sur le point de passage (ou dans l\'espace vide pour en créer un)');
      } else if (obj && isPointLike(obj)) {
        state.tempPoints.push({ pointId: obj.id });
        setStatus('Cliquez sur la droite de référence');
      } else setStatus('Cliquez d\'abord sur une droite ou un point');
    } else {
      const prev = state.tempPoints[0];
      let refLineId, pointId;
      if (prev.lineId) {
        const pt = (obj && isPointLike(obj)) ? obj : makePoint(wx, wy);
        refLineId = prev.lineId; pointId = pt.id;
      } else if (prev.pointId && obj && isLineLike(obj)) {
        refLineId = obj.id; pointId = prev.pointId;
      }
      if (refLineId && pointId) {
        const perp = { id: uid(), type: 'perpendicular', label: nextLineLabel(), color: nextColor(), lineWidth: 2, visible: true, refLineId, pointId, px: 0, py: 0, dx: 0, dy: 1 };
        push(perp); state.tempPoints = []; render();
      } else { setStatus('Cliquez sur la droite de référence'); }
    }
  },

  'perp-bisector'(wx, wy) {
    twoPointToolAction(wx, wy, (a, b) => {
      push({ id: uid(), type: 'perp-bisector', label: nextLineLabel(), color: nextColor(), lineWidth: 2, visible: true, p1id: a.id, p2id: b.id, px: 0, py: 0, dx: 0, dy: 1 });
    });
  },

  'angle-bisector'(wx, wy) {
    threePointToolAction(wx, wy, (a, v, b) => {
      push({ id: uid(), type: 'angle-bisector', label: nextLineLabel(), color: nextColor(), lineWidth: 2, visible: true, vertexId: v.id, p1id: a.id, p2id: b.id, px: 0, py: 0, dx: 1, dy: 0 });
    }, ['1er point de l\'angle', 'Sommet de l\'angle', '2ème point de l\'angle']);
  },

  polygon(wx, wy) {
    const snapped = snapToGrid(wx, wy);
    const existing = findNearPoint(wx, wy);
    // Close polygon on click near first point
    if (state.tempPoints.length >= 3) {
      const first = state.tempPoints[0];
      const c1 = worldToCanvas(first.x, first.y), cm = worldToCanvas(wx, wy);
      if (Math.hypot(cm.x - c1.x, cm.y - c1.y) < 12) {
        finishPolygon(); return;
      }
    }
    const pt = existing || makePoint(snapped.x, snapped.y);
    state.tempPoints.push({ x: pt.x, y: pt.y, id: pt.id });
    if (state.tempPoints.length === 1) setStatus('Cliquez pour ajouter des sommets — cliquez sur le 1er point pour fermer');
    render();
  },

  triangle(wx, wy) {
    twoPointToolAction(wx, wy, (a, b) => {
      const snapped = snapToGrid(wx, wy);
      const pt = makePoint(snapped.x, snapped.y);
      push({ id: uid(), type: 'polygon', label: nextPolygonLabel(), color: nextColor(), lineWidth: 2, visible: true, pointIds: [a.id, b.id, pt.id] });
    }, true);
  },

  rectangle(wx, wy) {
    twoPointToolAction(wx, wy, (a, b) => {
      const c = makePoint(b.x, a.y);
      const d = makePoint(a.x, b.y);
      push({ id: uid(), type: 'rect', label: nextPolygonLabel(), color: nextColor(), lineWidth: 2, visible: true,
             fillColor: '#7c9eff', fillOpacity: 0.15, zIndex: 0,
             pointIds: [a.id, c.id, b.id, d.id] });
    });
  },

  'circle-center-point'(wx, wy) {
    twoPointToolAction(wx, wy, (center, rPt) => {
      const r = dist(center, rPt);
      push({ id: uid(), type: 'circle', label: nextCircleLabel(), color: nextColor(), lineWidth: 2, visible: true, centerId: center.id, radiusPointId: rPt.id, r });
    });
  },

  'circle-3points'(wx, wy) {
    threePointToolAction(wx, wy, (a, b, c) => {
      push({ id: uid(), type: 'circle3pts', label: nextCircleLabel(), color: nextColor(), lineWidth: 2, visible: true, p1id: a.id, p2id: b.id, p3id: c.id });
    });
  },

  semicircle(wx, wy) {
    twoPointToolAction(wx, wy, (a, b) => {
      push({ id: uid(), type: 'semicircle', label: nextCircleLabel(), color: nextColor(), lineWidth: 2, visible: true, p1id: a.id, p2id: b.id });
    });
  },

  arc(wx, wy) {
    threePointToolAction(wx, wy, (a, b, c) => {
      const cc = circumcenter(a, b, c);
      if (!cc) { setStatus('Points alignés, impossible de tracer un arc'); return; }
      const r = dist(cc, a);
      const startAngle = Math.atan2(-(a.y - cc.y), a.x - cc.x);
      const endAngle = Math.atan2(-(c.y - cc.y), c.x - cc.x);
      const arc = { id: uid(), type: 'arc', label: nextCircleLabel(), color: nextColor(), lineWidth: 2, visible: true, centerId: uid(), r, startAngle, endAngle };
      // Fake center point (non-interactive)
      const centerPt = { id: arc.centerId, type: 'point', label: '', color: 'transparent', lineWidth: 0, visible: false, x: cc.x, y: cc.y };
      state.objects.push(centerPt);
      push(arc);
    });
  },

  angle(wx, wy) {
    threePointToolAction(wx, wy, (a, vertex, b) => {
      push({ id: uid(), type: 'angle-measure', label: nextAngleLabel(), color: '#f9e2af', lineWidth: 2, visible: true, vertexId: vertex.id, p1id: a.id, p2id: b.id, value: 0 });
    }, ['1er point', 'Sommet', '2ème point']);
  },

  distance(wx, wy) {
    twoPointToolAction(wx, wy, (a, b) => {
      push({ id: uid(), type: 'distance-measure', label: nextMeasureLabel(), color: '#89dceb', lineWidth: 2, visible: true, p1id: a.id, p2id: b.id, value: 0 });
    });
  },

  area(wx, wy) {
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (obj && obj.type === 'polygon') {
      push({ id: uid(), type: 'area-measure', label: nextMeasureLabel(), color: '#a6e3a1', lineWidth: 0, visible: true, polygonId: obj.id, value: 0 });
      render();
    } else { setStatus('Cliquez sur un polygone pour mesurer son aire'); }
  },

  'reflect-line'(wx, wy) {
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (!state.tempPoints.length) {
      if (obj && isPointLike(obj)) {
        state.tempPoints.push({ pointId: obj.id });
        setStatus('Cliquez sur l\'axe de symétrie');
      } else if (obj && isLineLike(obj)) {
        state.tempPoints.push({ lineId: obj.id });
        setStatus('Cliquez sur le point à réfléchir');
      } else setStatus('Cliquez sur un point ou une droite');
    } else {
      const prev = state.tempPoints[0];
      let srcId, lineId;
      if (prev.pointId && obj && isLineLike(obj)) { srcId = prev.pointId; lineId = obj.id; }
      else if (prev.lineId && obj && isPointLike(obj)) { srcId = obj.id; lineId = prev.lineId; }
      if (srcId && lineId) {
        const src = getObj(srcId);
        push({ id: uid(), type: 'reflect-line', label: nextPointLabel(), color: '#cba6f7', lineWidth: 2, visible: true, sourceId: srcId, refLineId: lineId, x: src.x, y: src.y });
        state.tempPoints = []; render();
      } else { setStatus('Sélection invalide'); state.tempPoints = []; }
    }
  },

  'reflect-point'(wx, wy) {
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (!state.tempPoints.length) {
      if (obj && isPointLike(obj)) {
        state.tempPoints.push({ id: obj.id, x: obj.x, y: obj.y, isSrc: true });
        setStatus('Cliquez sur le centre de symétrie');
      } else setStatus('Cliquez sur le point à réfléchir');
    } else {
      const prev = state.tempPoints[0];
      if (obj && isPointLike(obj)) {
        const src = getObj(prev.id);
        push({ id: uid(), type: 'reflect-point', label: nextPointLabel(), color: '#cba6f7', lineWidth: 2, visible: true, sourceId: prev.id, centerId: obj.id, x: src.x, y: src.y });
        state.tempPoints = []; render();
      } else setStatus('Cliquez sur le centre');
    }
  },

  rotate(wx, wy) {
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (!state.tempPoints.length) {
      if (obj && isPointLike(obj)) {
        state.tempPoints.push({ srcId: obj.id });
        setStatus('Cliquez sur le centre de rotation');
      } else setStatus('Cliquez sur le point à tourner');
    } else if (state.tempPoints.length === 1) {
      if (obj && isPointLike(obj)) {
        state.tempPoints.push({ centerId: obj.id });
        showInputDialog('Angle de rotation (degrés)', '45', (val) => {
          const angle = parseFloat(val);
          const prev = state.tempPoints;
          const src = getObj(prev[0].srcId);
          push({ id: uid(), type: 'rotate', label: nextPointLabel(), color: '#fab387', lineWidth: 2, visible: true, sourceId: prev[0].srcId, centerId: prev[1].centerId, angle, x: src.x, y: src.y });
          state.tempPoints = []; render();
        });
      } else setStatus('Cliquez sur le centre');
    }
  },

  translate(wx, wy) {
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (!state.tempPoints.length) {
      if (obj && isPointLike(obj)) {
        state.tempPoints.push({ srcId: obj.id });
        setStatus('Cliquez sur le 1er point du vecteur de translation');
      } else setStatus('Cliquez sur le point à translater');
    } else if (state.tempPoints.length === 1) {
      if (obj && isPointLike(obj)) { state.tempPoints.push({ v1Id: obj.id }); setStatus('2ème point du vecteur'); }
    } else if (state.tempPoints.length === 2) {
      if (obj && isPointLike(obj)) {
        const src = getObj(state.tempPoints[0].srcId);
        push({ id: uid(), type: 'translate', label: nextPointLabel(), color: '#fab387', lineWidth: 2, visible: true, sourceId: state.tempPoints[0].srcId, vec1Id: state.tempPoints[1].v1Id, vec2Id: obj.id, x: src.x, y: src.y });
        state.tempPoints = []; render();
      }
    }
  },

  text(wx, wy) {
    const content = prompt('Texte à afficher :');
    if (!content) return;
    push({ id: uid(), type: 'text', label: 't' + (++state.labelCounters.text), color: '#cdd6f4', lineWidth: 0, visible: true, x: wx, y: wy, text: content, fontSize: 16 });
    render();
  },

  delete(wx, wy) {
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (obj) deleteObject(obj.id);
  },

  select(wx, wy) {
    const obj = objectAtCanvas(...worldToCanvasPx((state.rawClickWorld||{x:wx,y:wy}).x, (state.rawClickWorld||{x:wx,y:wy}).y));
    if (obj) {
      state.selected = [obj.id];
      showProperties(obj);
    } else {
      state.selected = [];
      hideProperties();
    }
    render();
  }
};

// ── Tool helpers ──────────────────────────────────
function worldToCanvasPx(wx, wy) {
  const c = worldToCanvas(wx, wy);
  return [c.x, c.y];
}

function snapToObjectPoint(obj, wx, wy) {
  // Return closest point on line/circle
  if (isLineLike(obj)) {
    const p1 = getPoint(obj.p1id || 0), p2 = getPoint(obj.p2id || 0);
    if (!p1 || !p2) return { x: wx, y: wy };
    const dx = p2.x - p1.x, dy = p2.y - p1.y;
    const len2 = dx * dx + dy * dy;
    if (len2 < 1e-10) return { x: p1.x, y: p1.y };
    const t = ((wx - p1.x) * dx + (wy - p1.y) * dy) / len2;
    return { x: p1.x + t * dx, y: p1.y + t * dy };
  }
  return { x: wx, y: wy };
}

function findNearPoint(wx, wy) {
  const cPos = worldToCanvas(wx, wy);
  for (let i = state.objects.length - 1; i >= 0; i--) {
    const o = state.objects[i];
    if (!isPointLike(o) || !o.visible) continue;
    const c = worldToCanvas(o.x, o.y);
    if (Math.hypot(cPos.x - c.x, cPos.y - c.y) < 10) return o;
  }
  return null;
}

function twoPointTool(type) {
  return function(wx, wy) {
    twoPointToolAction(wx, wy, (a, b) => {
      push({ id: uid(), type, label: type === 'segment' || type === 'line' || type === 'ray' || type === 'vector' ? nextLineLabel() : nextPointLabel(), color: nextColor(), lineWidth: 2, visible: true, p1id: a.id, p2id: b.id });
    });
  };
}

function twoPointToolAction(wx, wy, cb, immediateThird) {
  const snapped = snapToGrid(wx, wy);
  const existing = findNearPoint(wx, wy);

  if (!state.tempPoints.length) {
    const pt = existing || makePoint(snapped.x, snapped.y);
    state.tempPoints.push({ id: pt.id, x: pt.x, y: pt.y });
    setStatus('Cliquez pour placer le 2ème point');
    render();
  } else {
    const pt = existing || makePoint(snapped.x, snapped.y);
    const a = getObj(state.tempPoints[0].id), b = pt;
    cb(a, b);
    state.tempPoints = [];
    render();
  }
}

function threePointToolAction(wx, wy, cb, statusMsgs) {
  const msgs = statusMsgs || ['1er point', '2ème point', '3ème point'];
  const snapped = snapToGrid(wx, wy);
  const existing = findNearPoint(wx, wy);
  const pt = existing || makePoint(snapped.x, snapped.y);
  state.tempPoints.push({ id: pt.id, x: pt.x, y: pt.y });

  if (state.tempPoints.length === 1) { setStatus(msgs[1] || 'Cliquez sur le 2ème point'); render(); return; }
  if (state.tempPoints.length === 2) { setStatus(msgs[2] || 'Cliquez sur le 3ème point'); render(); return; }

  const [a, b, c] = state.tempPoints.map(p => getObj(p.id));
  cb(a, b, c);
  state.tempPoints = [];
  render();
}

function finishPolygon() {
  if (state.tempPoints.length < 3) { setStatus('Un polygone nécessite au moins 3 points'); return; }
  push({ id: uid(), type: 'polygon', label: nextPolygonLabel(), color: nextColor(), lineWidth: 2, visible: true, pointIds: state.tempPoints.map(p => p.id) });
  state.tempPoints = [];
  render();
}

function deleteObject(id) {
  const idx = state.objects.findIndex(o => o.id === id);
  if (idx < 0) return;
  state.objects.splice(idx, 1);
  state.selected = state.selected.filter(sid => sid !== id);
  if (state.hover === id) state.hover = null;
  saveUndo();
  updateAlgebra();
  render();
  if (state._onObjectDeletedCb) state._onObjectDeletedCb(id);
}

// ── Group helpers ─────────────────────────────────
function joinGroup() {
  const sel = state.selected.slice();
  if (sel.length < 2) { setStatus('Sélectionnez au moins 2 objets à grouper'); return; }
  const memberIds = sel.filter(id => { const o = getObj(id); return o && o.type !== 'group'; });
  if (memberIds.length < 2) return;
  saveUndo();
  const grp = { id: uid(), type: 'group', label: 'grp' + (++state.labelCounters.line), memberIds };
  memberIds.forEach(id => { const o = getObj(id); if (o) o.groupId = grp.id; });
  state.objects.push(grp);
  state.selected = [grp.id];
  setStatus('Groupe créé : ' + grp.label);
  render();
  _fireAdd(grp.label);
}

function explodeGroup() {
  const groupIds = state.selected.filter(id => { const o = getObj(id); return o && o.type === 'group'; });
  if (groupIds.length === 0) {
    const gid = state.selected.map(id => getObjectGroupId(id)).find(Boolean);
    if (gid) groupIds.push(gid);
  }
  if (groupIds.length === 0) { setStatus('Sélectionnez un groupe à éclater'); return; }
  saveUndo();
  groupIds.forEach(groupId => {
    const g = getGroup(groupId);
    if (!g) return;
    g.memberIds.forEach(id => { const o = getObj(id); if (o) delete o.groupId; });
    state.objects = state.objects.filter(o => o.id !== groupId);
    if (state.editingGroupId === groupId) state.editingGroupId = null;
  });
  state.selected = [];
  setStatus('Groupe éclaté');
  render();
}

function enterGroupEdit(groupId) {
  state.editingGroupId = groupId;
  setStatus('Mode édition groupe — cliquez un membre pour l\'éditer individuellement');
  render();
}

function exitGroupEdit() {
  state.editingGroupId = null;
  setStatus('');
  render();
}

// ══════════════════════════════════════════════════════
// EVENTS
// ══════════════════════════════════════════════════════

function getCanvasPos(e) {
  const rect = canvas.getBoundingClientRect();
  const touch = e.touches ? e.touches[0] : e;
  return { x: touch.clientX - rect.left, y: touch.clientY - rect.top };
}

canvas.addEventListener('mousedown', e => {
  const pos = getCanvasPos(e);
  const world = canvasToWorld(pos.x, pos.y);

  if (e.button === 1 || (e.button === 0 && e.altKey)) {
    state.isPanning = true;
    state.panStart = { cx: pos.x, cy: pos.y, ox: state.ox, oy: state.oy };
    canvas.style.cursor = 'grabbing';
    e.preventDefault(); return;
  }

  if (e.button === 2 && !e.shiftKey) return;

  if (state.tool === 'select') {
    // Check if clicking a group pivot first
    const hitGroup = state.figureGroups.find(fg => {
      const pivot = state.objects.find(o => o.id === fg.pivotId || o.label === fg.pivotLabel);
      if (!pivot) return false;
      fg.pivotId = pivot.id; // keep pivotId in sync
      const c = worldToCanvas(pivot.x, pivot.y);
      return Math.hypot(c.x - pos.x, c.y - pos.y) <= 14;
    });
    if (hitGroup) {
      const pivot = state.objects.find(o => o.id === hitGroup.pivotId || o.label === hitGroup.pivotLabel);
      // Shift+clic sur pivot : déplace uniquement le pivot (reconfigure sa position)
      if (e.shiftKey && pivot && !state.exerciseMode) {
        state.selected = [pivot.id];
        state.isDragging = true;
        state.dragTarget = pivot;
        state.dragOffsetWorld = { x: pivot.x - world.x, y: pivot.y - world.y };
        state.dragLastWorld = { x: world.x, y: world.y };
        canvas.style.cursor = 'grabbing';
        render(); return;
      }
      state.isDraggingGroup = hitGroup.id;
      state.groupDragOffset = { dx: pivot.x - world.x, dy: pivot.y - world.y };
      state.groupDragOrigPos = { x: pivot.x, y: pivot.y };
      // Si le groupe était dans une zone verte, la repasser en active au début du drag
      if (state.exerciseMode) {
        const currentZone = getGroupZoneAt(pivot.x, pivot.y);
        if (currentZone && currentZone.state === 'green') currentZone.state = 'active';
      }
      canvas.style.cursor = 'grabbing';
      render(); return;
    }
    const obj = objectAtCanvas(pos.x, pos.y, true);
    // Shift+right-click: remove from selection
    if (e.button === 2 && e.shiftKey && obj) {
      state.selected = state.selected.filter(id => id !== obj.id);
      render(); return;
    }
    if (obj && isPointLike(obj)) {
      // Ctrl+click: toggle selection
      if (e.ctrlKey) {
        if (state.selected.includes(obj.id)) {
          state.selected = state.selected.filter(id => id !== obj.id);
        } else {
          state.selected = [...state.selected, obj.id];
        }
        render(); return;
      }
      // Group-aware click: if object belongs to a group and we're not editing that group
      if (obj.groupId && state.editingGroupId !== obj.groupId) {
        state.selected = [obj.groupId];
        const grp = getGroup(obj.groupId);
        if (grp) showProperties(grp);
        render(); return;
      }
      state.isDragging = true;
      state.dragTarget = obj.id;
      state.dragOffsetWorld = { x: obj.x - world.x, y: obj.y - world.y };
      state.selected = [obj.id];
      showProperties(obj);
      render(); return;
    }
    if (obj) {
      // Ctrl+click: toggle selection
      if (e.ctrlKey) {
        if (state.selected.includes(obj.id)) {
          state.selected = state.selected.filter(id => id !== obj.id);
        } else {
          state.selected = [...state.selected, obj.id];
        }
        render(); return;
      }
      // Start dragging non-point object (moves all its defining points)
      const ptIds = getDefiningPointIds(obj);
      if (ptIds.length > 0 || obj.type === 'text') {
        state.isDragging = true;
        state.dragTarget = obj.id;
        const snL = snapToGrid(world.x, world.y);
        state.dragLastWorld = { x: snL.x, y: snL.y };
        state.selected = [obj.id];
        showProperties(obj);
        canvas.style.cursor = 'grabbing';
        render(); return;
      }
      state.selected = [obj.id];
      showProperties(obj);
      render(); return;
    }
    if (e.shiftKey) {
      // Shift+drag: lasso selection
      state.isLasso = true;
      state.lassoStart = { cx: pos.x, cy: pos.y };
      state.lassoEnd = { cx: pos.x, cy: pos.y };
      state.selected = [];
      canvas.style.cursor = 'crosshair';
      render(); return;
    }
    // Start pan with left button if nothing hit
    state.isPanning = true;
    state.panStart = { cx: pos.x, cy: pos.y, ox: state.ox, oy: state.oy };
    canvas.style.cursor = 'grabbing';
    return;
  }

  if (state.tool === 'lasso') {
    state.isLasso = true;
    state.lassoStart = { cx: pos.x, cy: pos.y };
    state.lassoEnd = { cx: pos.x, cy: pos.y };
    state.selected = [];
    canvas.style.cursor = 'crosshair';
    render(); return;
  }

  const snapped = snapToGrid(world.x, world.y);
  state.rawClickWorld = world; // raw coords for hit-testing in tools
  const handler = toolHandlers[state.tool];
  if (handler) handler(snapped.x, snapped.y);
});

canvas.addEventListener('mousemove', e => {
  const pos = getCanvasPos(e);
  const world = canvasToWorld(pos.x, pos.y);
  state.mouseWorld = world;

  if (state.isPanning && state.panStart) {
    state.ox = state.panStart.ox - (pos.x - state.panStart.cx) / state.scale;
    state.oy = state.panStart.oy + (pos.y - state.panStart.cy) / state.scale;
    render(); return;
  }

  if (state.isLasso && state.lassoStart) {
    state.lassoEnd = { cx: pos.x, cy: pos.y };
    render(); return;
  }

  if (state.isDraggingGroup) {
    const fg = state.figureGroups.find(g => g.id === state.isDraggingGroup);
    if (fg) {
      const pivot = state.objects.find(o => o.id === fg.pivotId || o.label === fg.pivotLabel);
      if (pivot) {
        const snapped = snapToGrid(world.x + state.groupDragOffset.dx, world.y + state.groupDragOffset.dy);
        const ddx = snapped.x - pivot.x, ddy = snapped.y - pivot.y;
        // Move pivot
        pivot.x = snapped.x; pivot.y = snapped.y;
        // Move all group objects (use moveObjectBy to handle rects/polygons via their defining points)
        const movedSet = new Set([pivot.id]);
        fg.objectIds.forEach(oid => {
          const o = state.objects.find(ob => ob.id === oid);
          if (o) moveObjectBy(o, ddx, ddy, movedSet, true);
        });
        // Highlight zone under pivot (seulement en mode exercice)
        if (state.exerciseMode) {
          const zone = getGroupZoneAt(pivot.x, pivot.y);
          state.zones.forEach(z => { if (z.state !== 'green') z.state = 'active'; });
          if (zone && zone.state !== 'green') zone.state = 'yellow';
        }
        render();
      }
    }
    return;
  }

  if (state.isDragging && state.dragTarget) {
    const obj = getObj(state.dragTarget);
    if (obj && isPointLike(obj)) {
      const newPos = snapToGrid(world.x + state.dragOffsetWorld.x, world.y + state.dragOffsetWorld.y);
      const ddx = newPos.x - obj.x;
      const ddy = newPos.y - obj.y;
      obj.x = newPos.x; obj.y = newPos.y;
      // Move group members if in a group and not editing that group
      if (obj.groupId && state.editingGroupId !== obj.groupId) {
        getGroupMembers(obj.groupId).forEach(m => {
          if (m.id !== obj.id && isPointLike(m)) { m.x += ddx; m.y += ddy; }
        });
      }
      evalAll(); updateAlgebra();
      updatePropertiesLive(obj);
      render(); return;
    }
    // Drag non-point object (segment, circle, polygon, etc.) — move all defining points
    if (obj && state.dragLastWorld) {
      // Snap based on nearest defining point, not cursor center
      const ptIds = getDefiningPointIds(obj);
      let snapRef = world; // fallback: cursor
      if (ptIds.length > 0) {
        // Find the defining point closest to the cursor
        let best = null, bestDist = Infinity;
        ptIds.forEach(pid => {
          const pt = getObj(pid);
          if (pt) {
            const d = Math.hypot(pt.x - world.x, pt.y - world.y);
            if (d < bestDist) { bestDist = d; best = pt; }
          }
        });
        if (best) {
          // Snap that point to grid, derive delta from it
          const snapped = snapToGrid(best.x + (world.x - state.dragLastWorld.x), best.y + (world.y - state.dragLastWorld.y));
          const ddx = snapped.x - best.x;
          const ddy = snapped.y - best.y;
          if (ddx === 0 && ddy === 0) { render(); return; }
          state.dragLastWorld = { x: world.x, y: world.y };
          if (obj.groupId && state.editingGroupId !== obj.groupId) {
            const movedSet = new Set();
            getGroupMembers(obj.groupId).forEach(m => moveObjectBy(m, ddx, ddy, movedSet));
          } else {
            moveObjectBy(obj, ddx, ddy);
          }
          evalAll(); updateAlgebra();
          render(); return;
        }
      }
      const snappedDrag = snapToGrid(world.x, world.y);
      const ddx = snappedDrag.x - state.dragLastWorld.x;
      const ddy = snappedDrag.y - state.dragLastWorld.y;
      if (ddx === 0 && ddy === 0) { render(); return; }
      state.dragLastWorld = { x: snappedDrag.x, y: snappedDrag.y };
      if (obj.groupId && state.editingGroupId !== obj.groupId) {
        const movedSet = new Set();
        getGroupMembers(obj.groupId).forEach(m => moveObjectBy(m, ddx, ddy, movedSet));
      } else {
        moveObjectBy(obj, ddx, ddy);
      }
      evalAll(); updateAlgebra();
      render(); return;
    }
  }

  // Hover
  const hit = objectAtCanvas(pos.x, pos.y, state.tool === 'select');
  const newHover = hit ? hit.id : null;
  if (newHover !== state.hover) {
    state.hover = newHover;
    canvas.style.cursor = hit ? 'pointer' : (state.tool === 'select' || state.tool === 'lasso' ? 'default' : 'crosshair');
    render();
  }

  // Update coords display
  document.getElementById('coords-display').textContent =
    `x = ${world.x.toFixed(2)}, y = ${world.y.toFixed(2)}`;

  if (state.tempPoints.length) render();
});

canvas.addEventListener('mouseup', e => {
  if (state.isPanning) { state.isPanning = false; canvas.style.cursor = (state.tool === 'select' || state.tool === 'lasso') ? 'default' : 'crosshair'; }
  if (state.isDragging) {
    // If the dragged point is a pivot, update figureGroup startX/startY
    if (state.dragTarget) {
      const draggedId = state.dragTarget.id;
      const asFg = state.figureGroups.find(fg => fg.pivotId === draggedId || fg.pivotLabel === state.dragTarget.label);
      if (asFg && !state.exerciseMode) {
        asFg.startX = state.dragTarget.x;
        asFg.startY = state.dragTarget.y;
        if (state._onPivotMovedCb) state._onPivotMovedCb(asFg.id, state.dragTarget.x, state.dragTarget.y);
      }
    }
    state.isDragging = false; state.dragTarget = null; state.dragLastWorld = null; canvas.style.cursor = 'default'; saveUndo(); render();
  }
  if (state.isDraggingGroup) {
    const fg = state.figureGroups.find(g => g.id === state.isDraggingGroup);
    if (fg) {
      const pivot = state.objects.find(o => o.id === fg.pivotId || o.label === fg.pivotLabel);
      if (pivot) {
        const zone = getGroupZoneAt(pivot.x, pivot.y);
        const zoneId = zone ? zone.id : null;
        const inTarget = zoneId != null && fg.targetZoneId != null && zoneId === fg.targetZoneId;
        // Check alignment constraint (orthographic projection)
        let alignOk = true;
        if (inTarget && fg.alignConstraint && fg.alignConstraint.axis) {
          const ac = fg.alignConstraint;
          const refFg = state.figureGroups.find(g => g.id === ac.refGroupId);
          if (refFg) {
            const refBounds = getGroupBounds(refFg);
            const mobBounds = getGroupBounds(fg);
            const tol = ac.tolerance != null ? ac.tolerance : 0.5;
            if (ac.axis === 'x') {
              // Même colonne : les bords gauche ET droit de la figure mobile doivent coïncider
              // avec ceux de la référence (à tol près)
              alignOk = Math.abs(mobBounds.minX - refBounds.minX) <= tol
                     && Math.abs(mobBounds.maxX - refBounds.maxX) <= tol;
            } else if (ac.axis === 'y') {
              // Même ligne : les bords haut ET bas doivent coïncider
              alignOk = Math.abs(mobBounds.minY - refBounds.minY) <= tol
                     && Math.abs(mobBounds.maxY - refBounds.maxY) <= tol;
            }
          }
        }
        if (state.exerciseMode) {
          if (inTarget && alignOk) {
            if (zone) zone.state = 'green';
            if (state.groupMovedCallback) state.groupMovedCallback(fg.id, zoneId, pivot.x, pivot.y);
          } else if (inTarget) {
            // Bonne zone mais alignement incorrect
            if (zone && zone.state !== 'green') zone.state = 'yellow';
            if (state.groupMovedCallback) state.groupMovedCallback(fg.id, zoneId, pivot.x, pivot.y);
          } else {
            state.zones.forEach(z => { if (z.state !== 'green') z.state = 'active'; });
            if (state.groupMovedCallback) state.groupMovedCallback(fg.id, zoneId, pivot.x, pivot.y);
          }
        } else {
          // Éditeur : juste sauvegarder la nouvelle position du pivot
          saveUndo();
        }
        saveUndo();
      }
    }
    state.isDraggingGroup = null; state.groupDragOffset = null; state.groupDragOrigPos = null;
    canvas.style.cursor = 'default';
    render();
  }
  if (state.isLasso && state.lassoStart && state.lassoEnd) {
    const x1 = Math.min(state.lassoStart.cx, state.lassoEnd.cx);
    const y1 = Math.min(state.lassoStart.cy, state.lassoEnd.cy);
    const x2 = Math.max(state.lassoStart.cx, state.lassoEnd.cx);
    const y2 = Math.max(state.lassoStart.cy, state.lassoEnd.cy);
    if (x2 - x1 > 4 || y2 - y1 > 4) {
      const selected = [];
      state.objects.forEach(o => {
        if (!o.visible) return;
        let cx, cy;
        if (isPointLike(o)) { cx = o.x; cy = o.y; }
        else if (o.type === 'segment') {
          const p1 = getPoint(o.p1id), p2 = getPoint(o.p2id);
          if (p1 && p2) { cx = (p1.x + p2.x) / 2; cy = (p1.y + p2.y) / 2; }
        } else if (o.type === 'circle') {
          const c = getPoint(o.centerId);
          if (c) { cx = c.x; cy = c.y; }
        }
        if (cx == null) return;
        const cp = worldToCanvas(cx, cy);
        if (cp.x >= x1 && cp.x <= x2 && cp.y >= y1 && cp.y <= y2) selected.push(o.id);
      });
      state.selected = selected;
      if (selected.length === 1) { const obj = getObj(selected[0]); if (obj) showProperties(obj); }
      else hideProperties();
    }
    state.isLasso = false; state.lassoStart = null; state.lassoEnd = null;
    render();
  }
});

canvas.addEventListener('mouseleave', () => {
  state.mouseWorld = null;
  state.hover = null;
  if (state.isPanning) state.isPanning = false;
  if (state.isDragging) { state.isDragging = false; saveUndo(); }
  if (state.isLasso) { state.isLasso = false; state.lassoStart = null; state.lassoEnd = null; render(); }
});

canvas.addEventListener('wheel', e => {
  e.preventDefault();
  const pos = getCanvasPos(e);
  const worldBefore = canvasToWorld(pos.x, pos.y);
  const factor = e.deltaY < 0 ? 1.12 : 1 / 1.12;
  state.scale = Math.max(5, Math.min(2000, state.scale * factor));
  const worldAfter = canvasToWorld(pos.x, pos.y);
  state.ox -= worldAfter.x - worldBefore.x;
  state.oy -= worldAfter.y - worldBefore.y;
  updateZoomDisplay();
  render();
}, { passive: false });

canvas.addEventListener('contextmenu', e => e.preventDefault());

// Double-click to finish polygon
canvas.addEventListener('dblclick', e => {
  if (state.tool === 'polygon' && state.tempPoints.length >= 3) finishPolygon();
  // Enter group edit mode on double-click of selected group
  if (state.tool === 'select' && state.selected.length === 1) {
    const selObj = getObj(state.selected[0]);
    if (selObj && selObj.type === 'group') {
      enterGroupEdit(selObj.id);
    }
  }
});

// ── Keyboard shortcuts ────────────────────────────
document.addEventListener('keydown', e => {
  if (e.target.tagName === 'INPUT') return;
  if (e.ctrlKey || e.metaKey) {
    if (e.key === 'z') { e.preventDefault(); undo(); }
    if (e.key === 'y' || (e.shiftKey && e.key === 'z')) { e.preventDefault(); redo(); }
    if (e.key === 'g') { e.preventDefault(); joinGroup(); }
    if (e.key === 'a') { e.preventDefault(); toggleAxes(); }
    return;
  }
  switch (e.key) {
    case 's': case 'S': setTool('select'); break;
    case 'p': case 'P': setTool('point'); break;
    case 'm': case 'M': setTool('midpoint'); break;
    case 'g': case 'G': setTool('segment'); break;
    case 'd': case 'D': setTool('line'); break;
    case 'c': case 'C': setTool('circle-center-point'); break;
    case 'f': case 'F': fitView(); break;
    case '+': case '=': zoom(1.2); break;
    case '-': zoom(1 / 1.2); break;
    case 'Delete': case 'Backspace':
      if (state.selected.length) { state.selected.forEach(deleteObject); state.selected = []; }
      break;
    case 'Escape':
      if (state.editingGroupId) { exitGroupEdit(); break; }
      state.tempPoints = []; state.selected = []; hideProperties(); setTool('select'); render(); break;
  }
});

// ── Toolbar buttons ───────────────────────────────
document.querySelectorAll('.tool-btn').forEach(btn => {
  btn.addEventListener('click', () => setTool(btn.dataset.tool));
});

// ── Group buttons ─────────────────────────────────
const btnJoin = document.getElementById('btn-join-group');
if (btnJoin) btnJoin.addEventListener('click', joinGroup);
const btnExplode = document.getElementById('btn-explode-group');
if (btnExplode) btnExplode.addEventListener('click', explodeGroup);

function setTool(tool) {
  state.tool = tool;
  state.tempPoints = [];
  document.querySelectorAll('.tool-btn').forEach(b => b.classList.toggle('active', b.dataset.tool === tool));
  canvas.style.cursor = tool === 'select' ? 'default' : 'crosshair';

  const hints = {
    select: 'Cliquez pour sélectionner, glissez pour déplacer',
    point: 'Cliquez pour placer un point',
    'point-on-object': 'Cliquez sur un objet pour y placer un point',
    midpoint: 'Cliquez sur un segment ou deux points',
    intersect: 'Cliquez sur deux objets pour trouver leur intersection',
    segment: 'Cliquez pour le 1er point du segment',
    line: 'Cliquez pour le 1er point de la droite',
    ray: 'Cliquez pour l\'origine de la demi-droite',
    vector: 'Cliquez pour l\'origine du vecteur',
    parallel: 'Cliquez sur une droite, puis un point (ou inversement)',
    perpendicular: 'Cliquez sur une droite, puis un point',
    'perp-bisector': 'Cliquez sur deux points',
    'angle-bisector': 'Cliquez sur 3 points (1er point, sommet, 2ème point)',
    polygon: 'Cliquez pour ajouter des sommets — double-clic ou clic sur le 1er point pour fermer',
    triangle: 'Cliquez pour les deux premiers sommets',
    rectangle: 'Cliquez sur deux coins opposés',
    'circle-center-point': 'Cliquez pour le centre, puis un point sur le cercle',
    'circle-3points': 'Cliquez sur 3 points du cercle',
    semicircle: 'Cliquez sur les deux extrémités du diamètre',
    arc: 'Cliquez sur 3 points (début, milieu, fin)',
    angle: 'Cliquez sur 3 points (1er point, sommet, 2ème point)',
    distance: 'Cliquez sur deux points pour mesurer la distance',
    area: 'Cliquez sur un polygone pour mesurer son aire',
    'reflect-line': 'Cliquez sur un point, puis sur l\'axe de symétrie',
    'reflect-point': 'Cliquez sur le point à réfléchir, puis sur le centre',
    rotate: 'Cliquez sur le point à tourner, puis sur le centre',
    translate: 'Cliquez sur le point, puis sur les deux extrémités du vecteur',
    text: 'Cliquez pour placer le texte',
    delete: 'Cliquez sur un objet pour le supprimer',
  };
  setStatus(hints[tool] || '');
}

function setStatus(msg) { document.getElementById('status-message').textContent = msg; }

// ── Zoom / View ───────────────────────────────────
document.getElementById('btn-zoom-in').addEventListener('click', () => zoom(1.3));
document.getElementById('btn-zoom-out').addEventListener('click', () => zoom(1 / 1.3));
document.getElementById('btn-zoom-fit').addEventListener('click', fitView);

function zoom(factor) {
  state.scale = Math.max(5, Math.min(2000, state.scale * factor));
  updateZoomDisplay(); render();
}

function fitView() {
  const pts = state.objects.filter(o => isPointLike(o));
  if (!pts.length) { state.scale = 60; state.ox = 0; state.oy = 0; updateZoomDisplay(); render(); return; }
  const xs = pts.map(p => p.x), ys = pts.map(p => p.y);
  const minX = Math.min(...xs), maxX = Math.max(...xs);
  const minY = Math.min(...ys), maxY = Math.max(...ys);
  const W = canvas.width - 80, H = canvas.height - 80;
  const dX = maxX - minX || 10, dY = maxY - minY || 10;
  state.scale = Math.max(5, Math.min(400, Math.min(W / dX, H / dY) * 0.8));
  state.ox = (minX + maxX) / 2;
  state.oy = (minY + maxY) / 2;
  updateZoomDisplay(); render();
}

function updateZoomDisplay() {
  document.getElementById('zoom-level').textContent = Math.round(state.scale / 60 * 100) + '%';
}

// ── Grid / Axes toggles ───────────────────────────
document.getElementById('btn-grid').addEventListener('click', toggleGrid);
document.getElementById('btn-axes').addEventListener('click', toggleAxes);

function toggleGrid() {
  state.showGrid = !state.showGrid;
  document.getElementById('btn-grid').classList.toggle('active', state.showGrid);
  render();
}

function toggleAxes() {
  state.showAxes = !state.showAxes;
  document.getElementById('btn-axes').classList.toggle('active', state.showAxes);
  render();
}

// ── Snap controls ─────────────────────────────────
state.snapUnit = 1;
(function() {
  const btnSnap = document.getElementById('btn-snap');
  const selUnit = document.getElementById('snap-unit');
  if (btnSnap) {
    btnSnap.addEventListener('click', function() {
      const on = this.classList.toggle('active');
      state.snapUnit = on ? (parseFloat(selUnit ? selUnit.value : '1') || 1) : 0;
    });
  }
  if (selUnit) {
    selUnit.addEventListener('change', function() {
      state.snapUnit = parseFloat(this.value) || 1;
      if (btnSnap) btnSnap.classList.add('active');
    });
  }
})();

// ── Algebra panel ─────────────────────────────────
document.getElementById('toggle-algebra').addEventListener('click', () => {
  document.getElementById('algebra-panel').classList.toggle('collapsed');
});

function updateAlgebra() {
  evalAll();
  const list = document.getElementById('algebra-list');
  list.innerHTML = '';
  state.objects.forEach(obj => {
    if (!obj.label) return;
    const item = document.createElement('div');
    item.className = 'algebra-item' + (state.selected.includes(obj.id) ? ' selected' : '') + (!obj.visible ? ' hidden-obj' : '');
    item.dataset.id = obj.id;

    const dot = document.createElement('span');
    dot.className = 'algebra-color';
    dot.style.background = obj.color || '#7c9eff';

    const lbl = document.createElement('span');
    lbl.className = 'algebra-label';
    lbl.textContent = obj.label;

    const def = document.createElement('span');
    def.className = 'algebra-def';
    def.textContent = objectDescription(obj);

    const eye = document.createElement('button');
    eye.className = 'algebra-eye';
    eye.textContent = obj.visible ? '👁' : '🚫';
    eye.title = obj.visible ? 'Masquer' : 'Afficher';
    eye.addEventListener('click', ev => {
      ev.stopPropagation();
      obj.visible = !obj.visible;
      updateAlgebra(); render();
    });

    item.appendChild(dot); item.appendChild(lbl); item.appendChild(def); item.appendChild(eye);
    item.addEventListener('click', () => {
      state.selected = [obj.id];
      showProperties(obj);
      render(); updateAlgebra();
    });
    list.appendChild(item);
  });
}

function objectDescription(obj) {
  switch (obj.type) {
    case 'point': case 'midpoint': case 'reflect-line': case 'reflect-point':
    case 'rotate': case 'translate': case 'intersect':
      return `(${obj.x?.toFixed(2)}, ${obj.y?.toFixed(2)})`;
    case 'segment': { const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id); return p1 && p2 ? `|${dist(p1,p2).toFixed(2)}|` : ''; }
    case 'line': return 'droite';
    case 'ray': return 'demi-droite';
    case 'vector': { const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id); return p1 && p2 ? `→(${(p2.x-p1.x).toFixed(1)},${(p2.y-p1.y).toFixed(1)})` : ''; }
    case 'circle': case 'circle3pts': return `r=${obj.r?.toFixed(2) || '?'}`;
    case 'polygon': return `${obj.pointIds?.length || 0} sommets`;
    case 'angle-measure': return obj.value != null ? `${obj.value.toFixed(1)}°` : '';
    case 'distance-measure': return obj.value != null ? `${obj.value.toFixed(2)}` : '';
    case 'area-measure': return obj.value != null ? `${obj.value.toFixed(2)}` : '';
    case 'text': return `"${obj.text}"`;
    case 'group': return `${obj.memberIds?.length || 0} membres`;
    default: return '';
  }
}

// ── Properties panel ──────────────────────────────
function showProperties(obj) {
  const panel = document.getElementById('properties-panel');
  const title = document.getElementById('prop-title');
  const content = document.getElementById('properties-content');
  panel.classList.remove('hidden');

  const typeNames = {
    point: 'Point', midpoint: 'Milieu', segment: 'Segment', line: 'Droite',
    ray: 'Demi-droite', vector: 'Vecteur', circle: 'Cercle', circle3pts: 'Cercle',
    polygon: 'Polygone', rect: 'Rectangle', text: 'Texte', 'angle-measure': 'Angle',
    'distance-measure': 'Distance', 'area-measure': 'Aire', parallel: 'Parallèle',
    perpendicular: 'Perpendiculaire', 'perp-bisector': 'Médiatrice',
    'angle-bisector': 'Bissectrice', semicircle: 'Demi-cercle', arc: 'Arc',
    intersect: 'Intersection', 'reflect-line': 'Image (axiale)', 'reflect-point': 'Image (centrale)',
    rotate: 'Image (rotation)', translate: 'Image (translation)'
  };
  title.textContent = (typeNames[obj.type] || obj.type) + ' ' + obj.label;

  // Special rendering for group
  if (obj.type === 'group') {
    const members = getGroupMembers(obj.id);
    let html = '<div class="prop-row" style="flex-direction:column;align-items:flex-start">';
    html += '<label style="margin-bottom:4px">Membres :</label>';
    html += '<ul style="margin:0;padding-left:16px;font-size:12px">';
    members.forEach(m => { html += `<li>${m.label} (${m.type})</li>`; });
    html += '</ul></div>';
    html += `<div class="prop-row" style="gap:6px;margin-top:8px">`;
    html += `<button id="prop-enter-group" style="flex:1">✏️ Éditer dans le groupe</button>`;
    html += `<button id="prop-explode-group" style="flex:1">💥 Éclater</button>`;
    html += `</div>`;
    content.innerHTML = html;
    const btnEnter = content.querySelector('#prop-enter-group');
    if (btnEnter) btnEnter.addEventListener('click', () => enterGroupEdit(obj.id));
    const btnExplode = content.querySelector('#prop-explode-group');
    if (btnExplode) btnExplode.addEventListener('click', explodeGroup);
    return;
  }

  let html = '';

  // Measurement display
  if (obj.type === 'angle-measure' && obj.value != null)
    html += `<div class="prop-measure">${obj.value.toFixed(2)}°</div>`;
  if (obj.type === 'distance-measure' && obj.value != null)
    html += `<div class="prop-measure">${obj.value.toFixed(4)}</div>`;
  if (obj.type === 'area-measure' && obj.value != null)
    html += `<div class="prop-measure">${obj.value.toFixed(4)}</div>`;

  // Coordinates
  if (isPointLike(obj))
    html += `<div class="prop-row"><label>x</label><input type="number" id="px" step="0.5" value="${obj.x.toFixed(4)}"></div>
             <div class="prop-row"><label>y</label><input type="number" id="py" step="0.5" value="${obj.y.toFixed(4)}"></div>`;

  // Radius
  if (obj.type === 'circle' && obj.r != null)
    html += `<div class="prop-row"><label>r</label><input type="number" id="pr" step="0.1" value="${obj.r.toFixed(4)}" ${obj.radiusPointId ? 'readonly' : ''}></div>`;

  // Text
  if (obj.type === 'text')
    html += `<div class="prop-row"><label>Texte</label><input type="text" id="ptxt" value="${obj.text}"></div>`;

  // Rotation angle
  if (obj.type === 'rotate')
    html += `<div class="prop-row"><label>Angle</label><input type="number" id="pang" step="1" value="${obj.angle}">°</div>`;

  // Color
  html += `<div class="prop-row"><label>Couleur</label><input type="color" id="pcolor" value="${hexColor(obj.color || '#7c9eff')}"></div>`;
  // Fill (rect only)
  if (obj.type === 'rect') {
    html += `<div class="prop-row"><label>Remplissage</label><input type="color" id="pfillcolor" value="${hexColor(obj.fillColor || obj.color || '#7c9eff')}"></div>`;
    html += `<div class="prop-row"><label>Opacité</label><input type="range" id="pfillop" min="0" max="1" step="0.05" value="${obj.fillOpacity != null ? obj.fillOpacity : 0.15}" style="width:80px"><span id="pfillop-val">${Math.round((obj.fillOpacity != null ? obj.fillOpacity : 0.15)*100)}%</span></div>`;
    html += `<div class="prop-row"><label>Z-index</label><input type="number" id="pzindex" min="-10" max="10" step="1" value="${obj.zIndex || 0}" style="width:55px"></div>`;
  }
  // Line width + dashed toggle
  if (obj.type !== 'point' && !isPointLike(obj)) {
    html += `<div class="prop-row"><label>Épaisseur</label><input type="range" id="plw" min="1" max="8" value="${obj.lineWidth || 2}"></div>`;
    html += `<div class="prop-row"><label>Pointillé</label><input type="checkbox" id="pdashed" ${obj.dashed ? 'checked' : ''}></div>`;
  }
  // Visible
  html += `<div class="prop-row"><label>Visible</label><input type="checkbox" id="pvis" ${obj.visible ? 'checked' : ''}></div>`;
  // Label
  html += `<div class="prop-row"><label>Nom</label><input type="text" id="plabel" value="${obj.label}"></div>`;

  content.innerHTML = html;

  // Wire up inputs
  const bind = (id, cb) => { const el = content.querySelector('#' + id); if (el) el.addEventListener('input', cb); };
  bind('px', e => { if (obj.type === 'point') { obj.x = parseFloat(e.target.value) || 0; evalAll(); render(); updateAlgebra(); }});
  bind('py', e => { if (obj.type === 'point') { obj.y = parseFloat(e.target.value) || 0; evalAll(); render(); updateAlgebra(); }});
  bind('pr', e => { if (obj.type === 'circle' && !obj.radiusPointId) { obj.r = parseFloat(e.target.value) || 1; render(); }});
  bind('ptxt', e => { if (obj.type === 'text') { obj.text = e.target.value; render(); }});
  bind('pang', e => { if (obj.type === 'rotate') { obj.angle = parseFloat(e.target.value) || 0; evalAll(); render(); updateAlgebra(); }});
  bind('pcolor', e => { obj.color = e.target.value; render(); updateAlgebra(); });
  bind('pfillcolor', e => { obj.fillColor = e.target.value; render(); });
  bind('pfillop', e => {
    obj.fillOpacity = parseFloat(e.target.value);
    const v = content.querySelector('#pfillop-val');
    if (v) v.textContent = Math.round(obj.fillOpacity * 100) + '%';
    render();
  });
  bind('pzindex', e => { obj.zIndex = parseInt(e.target.value) || 0; render(); });
  bind('plw', e => { obj.lineWidth = parseInt(e.target.value); render(); });
  { const el = content.querySelector('#pdashed'); if (el) el.addEventListener('change', e => { obj.dashed = e.target.checked; render(); saveUndo(); }); }
  bind('pvis', e => { obj.visible = e.target.checked; render(); updateAlgebra(); });
  bind('plabel', e => { obj.label = e.target.value; updateAlgebra(); });
}

function updatePropertiesLive(obj) {
  const panel = document.getElementById('properties-panel');
  if (panel.classList.contains('hidden')) return;
  const px = panel.querySelector('#px'), py = panel.querySelector('#py');
  if (px) px.value = obj.x.toFixed(4);
  if (py) py.value = obj.y.toFixed(4);
  const desc = panel.querySelector('.prop-measure');
  if (desc) {
    if (obj.type === 'angle-measure' && obj.value != null) desc.textContent = obj.value.toFixed(2) + '°';
    if (obj.type === 'distance-measure' && obj.value != null) desc.textContent = obj.value.toFixed(4);
  }
}

function hideProperties() { document.getElementById('properties-panel').classList.add('hidden'); }
document.getElementById('prop-close').addEventListener('click', hideProperties);

function hexColor(c) {
  if (c.startsWith('#')) return c;
  const m = c.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)/);
  if (!m) return '#7c9eff';
  return '#' + [m[1], m[2], m[3]].map(n => parseInt(n).toString(16).padStart(2, '0')).join('');
}

// ── Clear / Export ────────────────────────────────
document.getElementById('btn-clear').addEventListener('click', () => {
  if (!confirm('Effacer tous les objets ?')) return;
  state.objects = [];
  state.selected = [];
  state.tempPoints = [];
  state.undoStack = [JSON.stringify([])];
  state.redoStack = [];
  state.labelCounters = { point: 0, line: 0, circle: 0, polygon: 0, text: 0, angle: 0, measure: 0 };
  colorIdx = 0;
  updateUndoButtons();
  updateAlgebra(); render();
});

document.getElementById('btn-undo').addEventListener('click', undo);
document.getElementById('btn-redo').addEventListener('click', redo);

document.getElementById('btn-export').addEventListener('click', () => {
  const link = document.createElement('a');
  link.download = 'geometrie.png';
  link.href = canvas.toDataURL();
  link.click();
});

// ── Input dialog ──────────────────────────────────
let _inputCallback = null;
function showInputDialog(title, defaultVal, cb) {
  _inputCallback = cb;
  document.getElementById('input-dialog-title').textContent = title;
  document.getElementById('input-dialog-field').value = defaultVal;
  document.getElementById('input-dialog').classList.remove('hidden');
  document.getElementById('input-dialog-field').focus();
  document.getElementById('input-dialog-field').select();
}

document.getElementById('input-dialog-ok').addEventListener('click', () => {
  const val = document.getElementById('input-dialog-field').value;
  document.getElementById('input-dialog').classList.add('hidden');
  if (_inputCallback) { _inputCallback(val); _inputCallback = null; }
});

document.getElementById('input-dialog-cancel').addEventListener('click', () => {
  document.getElementById('input-dialog').classList.add('hidden');
  _inputCallback = null; state.tempPoints = [];
});

document.getElementById('input-dialog-field').addEventListener('keydown', e => {
  if (e.key === 'Enter') document.getElementById('input-dialog-ok').click();
  if (e.key === 'Escape') document.getElementById('input-dialog-cancel').click();
});

// ── Resize ────────────────────────────────────────
function resizeCanvas() {
  const container = document.getElementById('canvas-container');
  canvas.width = container.clientWidth;
  canvas.height = container.clientHeight;
  render();
}

window.addEventListener('resize', resizeCanvas);

// ══════════════════════════════════════════════════════
// INIT
// ══════════════════════════════════════════════════════
resizeCanvas();
state.undoStack.push(JSON.stringify([]));
updateUndoButtons();
updateAlgebra();

// ══════════════════════════════════════════════════════
// geoApp PUBLIC API  (compatible GeoGebra ggbApplet)
// ══════════════════════════════════════════════════════

const geoVars = {};

const _geoListeners = {
  click: [],
  add: [],
  objectClick: {},   // name → [cb]
  objectUpdate: {}   // name → [cb]
};

function _fireAdd(label) {
  _geoListeners.add.forEach(cb => { try { cb(label); } catch(e) {} });
}
function _fireObjectUpdate(label) {
  (_geoListeners.objectUpdate[label] || []).forEach(cb => { try { cb(label); } catch(e) {} });
}

// Patch push/pushBatch to fire add listeners
const _origPush = push;
function push(obj) {
  state.objects.push(obj);
  saveUndo();
  updateAlgebra();
  _fireAdd(obj.label);
}

const geoApp = {

  // ── Object manipulation ──────────────────────────

  setCoords(name, x, y) {
    const obj = state.objects.find(o => o.label === name);
    if (!obj || obj.type !== 'point') return;
    obj.x = x; obj.y = y;
    evalAll(); render(); updateAlgebra();
    _fireObjectUpdate(name);
  },

  setFixed(name, fixed) {
    const obj = state.objects.find(o => o.label === name);
    if (obj) { obj.fixed = fixed; render(); }
  },

  setColor(name, r, g, b) {
    const obj = state.objects.find(o => o.label === name);
    if (obj) { obj.color = `rgb(${r},${g},${b})`; render(); updateAlgebra(); }
  },

  setLineStyle(name, style) {
    const obj = state.objects.find(o => o.label === name);
    if (obj) { obj.lineStyle = style; render(); }
  },

  setVisible(name, vis) {
    const obj = state.objects.find(o => o.label === name);
    if (obj) { obj.visible = vis; render(); updateAlgebra(); }
  },

  deleteObject(name) {
    const obj = state.objects.find(o => o.label === name);
    if (obj) { deleteObject(obj.id); evalAll(); }
  },

  onObjectDeleted(cb) { state._onObjectDeletedCb = cb; },

  setExerciseMode(on) { state.exerciseMode = !!on; },

  loadGeoState(objects) {
    state.objects = JSON.parse(JSON.stringify(objects || []));
    // Reset nextId to avoid collisions
    const maxId = state.objects.reduce((m, o) => Math.max(m, typeof o.id === 'number' ? o.id : 0), 0);
    if (maxId >= nextId) nextId = maxId + 1;
    evalAll(); render(); updateAlgebra();
  },

  setValue(name, val) { geoVars[name] = val; },
  getValue(name) { return geoVars[name]; },

  setAvailableTools(toolNames) {
    const tools = new Set(toolNames);
    document.querySelectorAll('.tool-btn[data-tool]').forEach(btn => {
      const show = tools.size === 0 || tools.has(btn.dataset.tool);
      btn.style.display = show ? '' : 'none';
    });
  },

  setMode(mode) {
    const map = { 0: 'select', 10: 'point', 15: 'segment' };
    const tool = map[mode];
    if (!tool) return;
    state.tool = tool;
    document.querySelectorAll('.tool-btn').forEach(b => b.classList.remove('active'));
    const btn = document.querySelector(`[data-tool="${tool}"]`);
    if (btn) btn.classList.add('active');
  },

  // ── Listeners ────────────────────────────────────

  registerClickListener(cb) { _geoListeners.click.push(cb); },

  registerObjectClickListener(name, cb) {
    (_geoListeners.objectClick[name] = _geoListeners.objectClick[name] || []).push(cb);
  },

  registerObjectUpdateListener(name, cb) {
    (_geoListeners.objectUpdate[name] = _geoListeners.objectUpdate[name] || []).push(cb);
  },

  registerAddListener(cb) { _geoListeners.add.push(cb); },

  // ── Exercise panel ───────────────────────────────

  setupExercise({ title, instructions, imageUrl, totalQuestions, maxScore }) {
    const panel = document.getElementById('exercise-panel');
    if (!panel) return;
    panel.classList.remove('hidden');
    document.getElementById('ex-title').textContent = title || '';
    document.getElementById('ex-instructions').textContent = instructions || '';
    const scoreMax = maxScore != null ? maxScore.toFixed(1) : (totalQuestions || 0);
    document.getElementById('ex-score').textContent = '0 / ' + scoreMax;
    document.getElementById('ex-question-num').textContent = '1 / ' + (totalQuestions || 0);
    const img = document.getElementById('ex-ref-image');
    if (imageUrl && img) { img.src = imageUrl; img.style.display = 'block'; }
    else if (img) img.style.display = 'none';
  },

  setQuestion(num, total) {
    const el = document.getElementById('ex-question-num');
    if (el) el.textContent = num + ' / ' + total;
  },

  setInstructions(text) {
    const el = document.getElementById('ex-instructions');
    if (el) el.textContent = text;
  },

  updateScore(score, total) {
    const el = document.getElementById('ex-score');
    if (el) el.textContent = score + ' / ' + total;
  },

  setZoneState(zoneId, zoneState) {
    const z = state.zones.find(z => z.id === zoneId);
    if (z) { z.state = zoneState; render(); }
    // Also update HTML div if present (legacy)
    const el = document.getElementById(zoneId);
    if (el) { el.dataset.state = zoneState; el.className = el.className.replace(/\bzone-state-\S+/g, ''); el.classList.add('zone-state-' + zoneState); }
  },

  showZones() {
    state.zonesVisible = true; render();
    const el = document.getElementById('ex-zones');
    if (el) el.style.display = '';
  },

  hideZones() {
    state.zonesVisible = false; render();
    const el = document.getElementById('ex-zones');
    if (el) el.style.display = 'none';
  },

  defineZones(activeZoneIds, zoneW, zoneH, gap) {
    state.zones = buildZoneLayout(activeZoneIds || [], zoneW, zoneH, gap);
    state.zonesVisible = activeZoneIds && activeZoneIds.length > 0;
    render();
  },

  defineFigureGroup(groupId, label, objectIds, pivotLabel, targetZoneId, targetX, targetY, tolerance, startX, startY, alignConstraint, mobile) {
    const pivot = state.objects.find(o => o.label === pivotLabel || o.id === pivotLabel);
    state.figureGroups = state.figureGroups.filter(g => g.id !== groupId);
    state.figureGroups.push({
      id: groupId, label: label || groupId,
      objectIds: objectIds || [],
      pivotId: pivot ? pivot.id : null,
      pivotLabel,
      targetZoneId: targetZoneId || null,
      targetX: targetX || 0, targetY: targetY || 0,
      tolerance: tolerance || 1,
      startX: startX != null ? startX : null,
      startY: startY != null ? startY : null,
      alignConstraint: alignConstraint || null,
      mobile: mobile !== false  // default true
    });
    render();
  },

  clearFigureGroups() {
    state.figureGroups = []; render();
  },

  onGroupMoved(callback) {
    state.groupMovedCallback = callback;
  },

  onPivotMoved(cb) { state._onPivotMovedCb = cb; },

  resetGroupToStart(groupId, targetX, targetY) {
    const fg = state.figureGroups.find(g => g.id === groupId);
    if (!fg) return;
    const pivot = state.objects.find(o => o.label === fg.pivotLabel || o.id === fg.pivotId);
    if (!pivot) return;
    const tx = targetX != null ? targetX : fg.startX;
    const ty = targetY != null ? targetY : fg.startY;
    if (tx == null) return;
    const ddx = tx - pivot.x, ddy = ty - pivot.y;
    // Move pivot and all defining points of member objects
    const movedPtIds = new Set();
    fg.objectIds.forEach(oid => {
      const o = state.objects.find(ob => ob.id === oid);
      if (!o) return;
      const ptIds = getDefiningPointIds(o);
      if (ptIds.length > 0) {
        ptIds.forEach(pid => {
          if (movedPtIds.has(pid)) return;
          movedPtIds.add(pid);
          const pt = state.objects.find(ob => ob.id === pid);
          if (pt) { pt.x += ddx; pt.y += ddy; }
        });
      } else if (isPointLike(o)) {
        if (!movedPtIds.has(o.id)) {
          movedPtIds.add(o.id);
          o.x += ddx; o.y += ddy;
        }
      }
    });
    // Also move pivot itself if not already moved
    if (!movedPtIds.has(pivot.id)) { pivot.x += ddx; pivot.y += ddy; }
    fg.currentZoneId = null;
    render();
  },

  resetAllGroupsToStart() {
    const mobileFgs = state.figureGroups.filter(fg => fg.mobile !== false);
    const n = mobileFgs.length;

    if (n > 0) {
      // Palette area: above the topmost zone
      const topZoneY2 = state.zones.reduce((m, z) => Math.max(m, z.y2), 5);
      const paletteY = topZoneY2 + 3;
      const totalW = state.zones.reduce((m, z) => Math.max(m, z.x2) - Math.min(0, z.x1), 20);
      const slotW  = Math.max(4, totalW / (n + 1));
      const indices = Array.from({ length: n }, (_, i) => i).sort(() => Math.random() - 0.5);
      const leftX = -(n - 1) * slotW / 2;

      mobileFgs.forEach((fg, i) => {
        const slot = indices[i];
        const jitter = (Math.random() - 0.5) * slotW * 0.4;
        const tx = leftX + slot * slotW + jitter;
        const ty = paletteY + (Math.random() - 0.5) * 1.5;
        this.resetGroupToStart(fg.id, tx, ty);
      });
    }

    // Reset zone states
    state.zones.forEach(z => { z.state = 'active'; });
    render();
  },

  // ── evalCommand ───────────────────────────────────

  evalCommand(cmd) {
    cmd = cmd.trim();

    // Point assignment: name = Point(x, y)
    const ptMatch = cmd.match(/^(\w+)\s*=\s*Point\(\s*([^,]+)\s*,\s*([^)]+)\s*\)$/i);
    if (ptMatch) {
      const name = ptMatch[1], x = parseFloat(ptMatch[2]), y = parseFloat(ptMatch[3]);
      const existing = state.objects.find(o => o.label === name);
      if (existing && isPointLike(existing)) {
        existing.x = x; existing.y = y; evalAll(); render(); updateAlgebra();
      } else {
        const obj = { id: uid(), type: 'point', label: name, x, y,
          color: '#7c9eff', lineWidth: 2, visible: true, fixed: false };
        state.objects.push(obj);
        evalAll(); render(); updateAlgebra();
        _fireAdd(name);
      }
      return name;
    }

    // Segment: name = Segment(p1, p2)
    const segMatch = cmd.match(/^(\w+)\s*=\s*Segment\((\w+)\s*,\s*(\w+)\)$/);
    if (segMatch) {
      const [, name, p1name, p2name] = segMatch;
      const p1 = state.objects.find(o => o.label === p1name);
      const p2 = state.objects.find(o => o.label === p2name);
      if (p1 && p2) {
        const existing = state.objects.find(o => o.label === name);
        if (existing) { existing.p1id = p1.id; existing.p2id = p2.id; evalAll(); render(); updateAlgebra(); return name; }
        const seg = { id: uid(), type: 'segment', label: name, color: '#7c9eff', lineWidth: 2, visible: true, fixed: false, p1id: p1.id, p2id: p2.id };
        state.objects.push(seg);
        evalAll(); render(); updateAlgebra();
        _fireAdd(name);
        return name;
      }
      return null;
    }

    // SetDynamicColor(name, r, g, b)
    const colorMatch = cmd.match(/^SetDynamicColor\(\s*(\w+)\s*,\s*([^,]+)\s*,\s*([^,]+)\s*,\s*([^)]+)\s*\)$/i);
    if (colorMatch) {
      const [, name, r, g, b] = colorMatch;
      geoApp.setColor(name, Math.round(parseFloat(r) * 255), Math.round(parseFloat(g) * 255), Math.round(parseFloat(b) * 255));
      return;
    }

    // ZoomIn / ZoomOut
    if (/^ZoomIn\b/i.test(cmd)) { state.scale = Math.min(state.scale * 1.3, 400); render(); return; }
    if (/^ZoomOut\b/i.test(cmd)) { state.scale = Math.max(state.scale / 1.3, 5); render(); return; }

    // AreEqual(a, b) → boolean
    const eqMatch = cmd.match(/^AreEqual\(\s*(\w+)\s*,\s*(\w+)\s*\)$/i);
    if (eqMatch) {
      const a = geoVars[eqMatch[1]], b = geoVars[eqMatch[2]];
      return a === b;
    }

    // Simple assignment: name = value
    const assignMatch = cmd.match(/^(\w+)\s*=\s*(.+)$/);
    if (assignMatch) {
      const val = assignMatch[2].trim();
      geoVars[assignMatch[1]] = isNaN(val) ? val : parseFloat(val);
    }
  },

  loadExerciseFromText(jsCode) {
    try {
      // eslint-disable-next-line no-new-func
      new Function('geoApp', 'geoVars', jsCode)(geoApp, geoVars);
    } catch (e) {
      console.error('Erreur chargement exercice:', e);
      alert('Erreur lors du chargement de l\'exercice:\n' + e.message);
    }
  },

  // ── Introspection (for exercise validation) ───────

  getAllObjects() {
    return state.objects.map(obj => {
      const info = { label: obj.label, type: obj.type, visible: obj.visible, fixed: !!obj.fixed, dashed: !!obj.dashed };
      if (isPointLike(obj)) { info.x = obj.x; info.y = obj.y; }
      if (obj.type === 'segment' || obj.type === 'line' || obj.type === 'ray' || obj.type === 'vector') {
        const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
        if (p1 && p2) { info.p1 = { x: p1.x, y: p1.y }; info.p2 = { x: p2.x, y: p2.y }; }
      }
      if (obj.type === 'circle' || obj.type === 'circle3pts') {
        const c = obj.centerId ? getPoint(obj.centerId) : { x: obj.cx, y: obj.cy };
        if (c) { info.cx = c.x; info.cy = c.y; info.r = obj.r; }
      }
      return info;
    });
  },

  getObjectCoords(name) {
    const obj = state.objects.find(o => o.label === name);
    if (!obj) return null;
    if (isPointLike(obj)) return { x: obj.x, y: obj.y };
    if (obj.type === 'segment' || obj.type === 'line') {
      const p1 = getPoint(obj.p1id), p2 = getPoint(obj.p2id);
      return p1 && p2 ? { p1, p2 } : null;
    }
    return null;
  },

  joinSelection() { joinGroup(); },
  explodeSelection() { explodeGroup(); },
  enterGroupEdit(groupId) { enterGroupEdit(groupId); },
  exitGroupEdit() { exitGroupEdit(); },
};

// ── Wire canvas click → geoApp click listeners ────
canvas.addEventListener('click', e => {
  const rect = canvas.getBoundingClientRect();
  const w = canvasToWorld(e.clientX - rect.left, e.clientY - rect.top);
  _geoListeners.click.forEach(cb => { try { cb(w.x, w.y); } catch(err) {} });
  const hit = objectAtCanvas(e.clientX - rect.left, e.clientY - rect.top);
  if (hit) {
    (_geoListeners.objectClick[hit.label] || []).forEach(cb => { try { cb(hit.label); } catch(err) {} });
  }
});

// ── Exercise panel button wiring ──────────────────
document.addEventListener('DOMContentLoaded', () => {
  const btnValidate = document.getElementById('ex-btn-validate');
  const btnNext     = document.getElementById('ex-btn-next');
  const btnReset    = document.getElementById('ex-btn-reset');
  const fileInput   = document.getElementById('ex-file-input');

  if (btnValidate) btnValidate.addEventListener('click', () => {
    const fn = geoVars['__onValidate'];
    if (typeof fn === 'function') fn();
  });
  if (btnNext) btnNext.addEventListener('click', () => {
    const fn = geoVars['__onNext'];
    if (typeof fn === 'function') fn();
  });
  if (btnReset) btnReset.addEventListener('click', () => {
    if (!confirm('Réinitialiser l\'exercice ?')) return;
    const fn = geoVars['__onReset'];
    if (typeof fn === 'function') fn();
  });
  if (fileInput) fileInput.addEventListener('change', e => {
    const file = e.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = ev => geoApp.loadExerciseFromText(ev.target.result);
    reader.readAsText(file);
    e.target.value = '';
  });

  // ── Left panel tabs ─────────────────────────────
  document.querySelectorAll('.left-tab').forEach(tab => {
    tab.addEventListener('click', () => {
      document.querySelectorAll('.left-tab').forEach(t => t.classList.remove('active'));
      document.querySelectorAll('.tab-content').forEach(c => c.style.display = 'none');
      tab.classList.add('active');
      const target = document.getElementById('tab-' + tab.dataset.tab);
      if (target) target.style.display = 'flex';
    });
  });

  // ── Exercise code editor (left panel) ────────────
  const codeEditor = document.getElementById('ex-code-editor');
  const codeLog    = document.getElementById('ex-code-log');

  function logCode(msg, type = 'ok') {
    codeLog.classList.add('has-log');
    const line = document.createElement('div');
    line.className = 'log-' + type;
    line.textContent = msg;
    codeLog.appendChild(line);
    codeLog.scrollTop = codeLog.scrollHeight;
  }

  const btnRun = document.getElementById('ex-btn-run');
  if (btnRun) btnRun.addEventListener('click', () => {
    const code = codeEditor ? codeEditor.value.trim() : '';
    if (!code) return;
    codeLog.innerHTML = '';
    codeLog.classList.remove('has-log');
    try {
      geoApp.loadExerciseFromText(code);
      logCode('✔ Exercice exécuté avec succès.', 'ok');
    } catch (e) {
      logCode('✕ Erreur : ' + e.message, 'err');
    }
  });

  const btnClearCode = document.getElementById('ex-btn-clear-code');
  if (btnClearCode) btnClearCode.addEventListener('click', () => {
    if (codeEditor) codeEditor.value = '';
    codeLog.innerHTML = '';
    codeLog.classList.remove('has-log');
  });

  // Charger un .js dans l'éditeur de code (panneau gauche)
  const leftFileInput = document.getElementById('ex-left-file-input');
  if (leftFileInput) leftFileInput.addEventListener('change', e => {
    const file = e.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = ev => {
      if (codeEditor) codeEditor.value = ev.target.result;
      // Switcher vers l'onglet Exercice
      document.querySelectorAll('.left-tab').forEach(t => t.classList.remove('active'));
      document.querySelectorAll('.tab-content').forEach(c => c.style.display = 'none');
      const tab = document.querySelector('[data-tab="exercise"]');
      const panel = document.getElementById('tab-exercise');
      if (tab) tab.classList.add('active');
      if (panel) panel.style.display = 'flex';
      logCode('📂 Fichier chargé : ' + file.name, 'ok');
      codeLog.classList.add('has-log');
    };
    reader.readAsText(file);
    e.target.value = '';
  });

  // Tab indentation dans l'éditeur
  if (codeEditor) codeEditor.addEventListener('keydown', e => {
    if (e.key === 'Tab') {
      e.preventDefault();
      const s = codeEditor.selectionStart;
      codeEditor.value = codeEditor.value.slice(0, s) + '  ' + codeEditor.value.slice(codeEditor.selectionEnd);
      codeEditor.selectionStart = codeEditor.selectionEnd = s + 2;
    }
  });

  // ── Chargement automatique depuis l'éditeur (bouton Tester) ──
  const urlParams = new URLSearchParams(window.location.search);
  if (urlParams.get('autoload') === '1') {
    const pendingCode = localStorage.getItem('geoapp_pending_exercise');
    if (pendingCode) {
      localStorage.removeItem('geoapp_pending_exercise');
      // Basculer vers l'onglet Exercice et afficher le code
      const tabEx = document.querySelector('[data-tab="exercise"]');
      const panelEx = document.getElementById('tab-exercise');
      document.querySelectorAll('.left-tab').forEach(t => t.classList.remove('active'));
      document.querySelectorAll('.tab-content').forEach(c => c.style.display = 'none');
      if (tabEx) tabEx.classList.add('active');
      if (panelEx) panelEx.style.display = 'flex';
      if (codeEditor) codeEditor.value = pendingCode;
      // Exécuter automatiquement
      setTimeout(() => {
        try {
          geoApp.loadExerciseFromText(pendingCode);
          logCode('▶ Exercice chargé depuis l\'éditeur.', 'ok');
        } catch(e) {
          logCode('✕ Erreur : ' + e.message, 'err');
        }
      }, 100);
    }
  }
});
