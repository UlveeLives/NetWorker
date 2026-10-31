/*! NetWorkKing — © 2026 Ulvi Badalov. Bütün hüquqlar qorunur / All rights reserved. Proprietary — see LICENSE. */
// Building structure: floors and rooms of every building, drawn on a floor plan by drag and drop, with small ready-made
// shapes for structure (rooms, corridors, stairs, lifts, doors, windows, columns) and devices (data outlets, APs, cameras,
// TVs, phones, racks …). A guided set-up asks for floors, rooms, server rooms and what each room needs.
// Everything is shared building data: rooms with a plan rectangle are the same rooms Wi-Fi Plan uses, devices placed here
// are the same devices in every other app.
"use strict";
(function(){
const RT = {office:["#e8f0ff","#2f5fc4"], meeting:["#f1e8ff","#6a3aa0"], server:["#ffe9e6","#b3262f"], corridor:["#f2f3f5","#7b8494"], lobby:["#e6f6ef","#1f8a5a"],
  kitchen:["#fff4e0","#b26a00"], wc:["#e9f6fb","#11706f"], storage:["#f5efe6","#8a6d3b"], technical:["#eceff3","#3a4552"], outdoor:["#eef7e6","#3d7a1f"], other:["#f7f7f7","#59607a"]};
const RTYPES = Object.keys(RT);
// what a room can need (requirement counts), in this order everywhere
const RK = ["outlet","ap","camera","tv","phone","printer","pc","access","intercom","touch","sensor","iot"];
const RK_SHORT = {outlet:"D", ap:"AP", camera:"CAM", tv:"TV", phone:"TEL", printer:"PRN", pc:"PC", access:"ACS", intercom:"INT", touch:"TP", sensor:"SNS", iot:"IoT"};
// default needs per room type (the set-up fills these in; the user changes them)
const RDEF = {outdoor:{camera:1}, office:{outlet:4, phone:1}, meeting:{outlet:2, tv:1}, server:{outlet:2, camera:1, access:1}, corridor:{camera:1}, lobby:{outlet:2, camera:1, tv:1, access:1},
  kitchen:{outlet:1}, wc:{}, storage:{}, technical:{outlet:1}, other:{outlet:2}};
// structure shapes (not devices)
const ITEMS = {yard:{w:30, h:20}, stairs:{w:3, h:5}, elevator:{w:2, h:2}, shaft:{w:1, h:1}, door:{w:1, h:.2}, window:{w:1.5, h:.2}, column:{w:.5, h:.5}, label:{w:4, h:1}};
const itemDef = k => ITEMS[k] || (DRAW.SYM[k] ? {w:DRAW.SYM[k][0], h:DRAW.SYM[k][1]} : {w:1, h:1});
const itemName = k => { const a = t("bi_" + k); return a === "bi_" + k ? k : a; };
const DEVK = ukList(["outlet","ap","camera","tv","phone","printer","pc","laptop","access","intercom","alarm","touch","sensor","iot","switch","nvr","decoder","server","ups","workstation","monitor"], "building");
let drag = null, place = null, lastDown = null, poly = null;
// apps that show this floor plan: Building structure (everything) and CCTV (cameras on the plan, rooms locked)
const HOSTS = {building:{tab:"plan"}, cctv:{tab:"plan", kinds:ukList(["camera","nvr","dvr","decoder","encoder","switch","monitor","workstation","videowall","joystick","poeinj","access","intercom","alarm"], "cctvplan"), cams:true, lockRooms:true}};
const host = () => HOSTS[UI.app] || null;
const onPlanTab = () => !!host() && curTab().id === host().tab;
const st = () => { UI.bld = UI.bld || {labels:true, grid:true}; return UI.bld; };

/* ---------- helpers ---------- */
const plan = f => f.plan;
const isSite = f => !!f && f.id === OUT_FLOOR;
const curFloor = b => { const S = st(); if (S.floor === OUT_FLOOR) return siteOf(b); let f = b.floors.find(x => x.id === S.floor); if (!f){ f = b.floors[0] || null; S.floor = f ? f.id : null; } return f; };
const roomsOf = (b, f) => b.rooms.filter(r => r.floor === f.id);
const geoRooms = (b, f) => roomsOf(b, f).filter(r => r.geo);
function normRoom(r){ r.type = RT[r.type] ? r.type : (/server|serv/i.test(r.name) ? "server" : /dəhliz|koridor|corridor|holl/i.test(r.name) ? "corridor" : OUTDOOR_RX.test(r.name) && !(r.geo && r.floor && r.floor !== OUT_FLOOR) ? "outdoor" : "office"); r.req = r.req && typeof r.req === "object" ? r.req : {}; for (const k in r.req) r.req[k] = clamp(Math.round(num(r.req[k], 0)), 0, 200); return r; }
function posOf(d){ if (d.kind === "ap") return d.ap && d.ap.x !== null && d.ap.x !== undefined && d.ap.x !== "" ? {x:num(d.ap.x), y:num(d.ap.y)} : null; return d.pos && d.pos.x !== undefined ? {x:num(d.pos.x), y:num(d.pos.y)} : null; }
function setPos(d, x, y){ if (d.kind === "ap"){ d.ap.x = r2(x); d.ap.y = r2(y); } else d.pos = {x:r2(x), y:r2(y)}; }
function clearPos(d){ if (d.kind === "ap"){ d.ap.x = null; d.ap.y = null; } else delete d.pos; }
const devFloor = (b, d) => d.floor || (d.room && (roomById(b, d.room) || {}).floor) || "";
const roomAtPt = (b, f, x, y) => { const L = geoRooms(b, f).filter(r => x >= r.geo.x && x <= r.geo.x + r.geo.w && y >= r.geo.y && y <= r.geo.y + r.geo.h); return L.filter(r => r.type !== "corridor")[0] || L[0] || null; };
const placedIn = (b, r, k) => b.devices.filter(d => d.room === r.id && d.kind === k).length;
const reqOf = (r, k) => clamp(Math.round(num(r.req && r.req[k])), 0, 200);
const area = r => !r.geo ? 0 : r.geo.area && r.geo.pw ? r1(r.geo.area * (r.geo.w / r.geo.pw) * (r.geo.h / r.geo.ph)) : r1(r.geo.w * r.geo.h);
function fixFloorPlan(f){ const p = f.plan; p.items = Array.isArray(p.items) ? p.items : []; f.h = f.h || 3.5; return p; }
// the grid catches at 0,5 m; holding Alt (or Ctrl) while dragging, or with the grid off, a point goes to the centimetre
let FINE = false;
document.addEventListener("keydown", e => { FINE = e.altKey || e.ctrlKey || e.metaKey; }); document.addEventListener("keyup", e => { FINE = e.altKey || e.ctrlKey || e.metaKey; });
document.addEventListener("pointermove", e => { FINE = e.altKey || e.ctrlKey || e.metaKey; }, true);
function snap(v){ return st().grid && !FINE ? Math.round(v * 2) / 2 : r2(v); }
// room outline from a drawing: points relative to the room box, stretched with it when the box is resized
function polyPts(g, s){ const sx = g.pw ? g.w / g.pw : 1, sy = g.ph ? g.h / g.ph : 1, P = g.poly, o = []; for (let i = 0; i + 1 < P.length; i += 2) o.push(((g.x + P[i] * sx) * s).toFixed(1) + "," + ((g.y + P[i + 1] * sy) * s).toFixed(1)); return o.join(" "); }
// room type from its name (Azerbaijani, Turkish, English, Russian)
function guessType(n){ const x = String(n).toLocaleLowerCase("tr");
  return /server|sistem otağı|sistem odası|serverna|data ?center|rack/.test(x) ? "server" : /teknik|texniki|elektrik|technical|kazan|boiler|pano|mechan|электр|технич/.test(x) ? "technical"
    : /wc|banyo|duş|dus|tualet|hamam|sauna|lavabo|bath|toilet|shower|санузел|ванн|туалет/.test(x) ? "wc" : /mutfak|mətbəx|metbex|kitchen|şark|şarküt|кухн/.test(x) ? "kitchen"
    : /koridor|dəhliz|corridor|hol\b|holü|holu|hall|antre|коридор|холл/.test(x) ? "corridor" : /salon|lobi|lobby|foye|rüzgarlık|ruzgarlik|giriş|giris|вестиб/.test(x) ? "lobby"
    : /toplantı|iclas|meeting|conference|konferans|переговор/.test(x) ? "meeting" : /depo|anbar|storage|kiler|çamaşır|camasir|giyinme|qarderob|garderob|склад|кладов/.test(x) ? "storage"
    : /oda|otaq|room|office|ofis|kabinet|çalışma|calisma|yatak|bedroom|master|кабинет|комнат|спальн/.test(x) ? "office" : "other"; }

/* ---------- the floor plan (SVG) ---------- */
// free space around the floor (metres): room for the yard, gates, outdoor cameras; grows with whatever is placed outside
function extOf(b, f, print){
  const p = f.plan; let x0 = 0, y0 = 0, x1 = p.wm, y1 = p.hm;
  const add = (x, y, w = 0, h = 0) => { if (!isFinite(x) || !isFinite(y)) return; x0 = Math.min(x0, x); y0 = Math.min(y0, y); x1 = Math.max(x1, x + w); y1 = Math.max(y1, y + h); };
  geoRooms(b, f).forEach(r => add(r.geo.x, r.geo.y, r.geo.w, r.geo.h)); (p.items || []).forEach(it => add(it.x, it.y, it.w, it.h)); (p.shapes || []).forEach(o => add(o.x, o.y, o.w, o.h)); DRAW.shownWalls(p).forEach(w => { add(w.x1, w.y1); add(w.x2, w.y2); });
  b.devices.forEach(d => { if (devFloor(b, d) !== f.id) return; const q = posOf(d); if (q) add(q.x, q.y); }); b.racks.forEach(r => { if (r.floor === f.id && r.pos) add(r.pos.x, r.pos.y); });
  const need = Math.max(-x0, -y0, x1 - p.wm, y1 - p.hm), pad = need > 0 ? need + (print ? 1.5 : 6) : 0;
  return Math.ceil(Math.max(print ? 0 : num(p.ext, 15), pad));
}
// pixels per metre: fixed for a floor (zoom and fit are done by the zoom / pan frame), so the plan never changes size under
// the pointer when the side panel opens or closes
function scaleFor(f){ return clamp(1100 / Math.max(4, num(f.plan.wm, 40)), 6, 70); }
// handle above a selected shape to turn it freely (Shift: steps of 15°)
const rotHandle = (key, x, y) => `<line x1="${x}" y1="${y}" x2="${x}" y2="${y - 22}" stroke="#ffb703" stroke-width="1.5" pointer-events="none"/><circle class="brot" data-brot="${key}" cx="${x}" cy="${y - 26}" r="7" fill="#ffb703" stroke="#7a5600" stroke-width="1.5"><title>${esc(t("dw_rotH"))}</title></circle>`;
// an invisible, generous area around a room name, so the name is easy to grab and move
function labHit(r, g, s, x, y){ const fs = g.lx !== undefined ? clamp(s * .38, 9, 13) : clamp(s * .45, 10, 14), tw = String(r.name).length * fs * .62 + 18, th = fs + 14;
  const cx = g.lx !== undefined ? (g.x + g.lx * (g.pw ? g.w / g.pw : 1)) * s : x + 6 + tw / 2 - 9, cy = g.lx !== undefined ? (g.y + g.ly * (g.ph ? g.h / g.ph : 1)) * s - fs * .35 : y + 15 - fs * .35;
  return `<rect class="rlabh" data-rlab="${r.id}" x="${(cx - tw / 2).toFixed(1)}" y="${(cy - th / 2).toFixed(1)}" width="${tw.toFixed(1)}" height="${th.toFixed(1)}" fill="transparent"/>`; }
// what blocks a camera's view on this plan. With a vector drawing (from DXF): the drawn wall, outer wall, window, door and
// column outlines — exactly what is seen; otherwise the walls (also those taken from a drawing, which are not shown). Doors
// block too (a camera does not look through a closed door; a garage camera stays in the garage) unless marked open on their
// card (a door wall, or a drawn piece holding doors — split it to open one door). Not blocking: low walls (a
// retaining wall or parapet the camera looks over). Also the outlines of the plot and houses. Curved walls go in short pieces.
const SH_BLOCK = /^(wall|wallExt|window|door|column)(:f)?$/;
// the blocking line pieces of a drawn shape in its own coordinates, read once per drawing (kept with the path list)
const SHSEG = new WeakMap();
// the lines of a drawing piece that stop a camera: walls, windows, doors (unless open) and columns; «blocks the cameras» on the
// piece's card makes every line of it count (sh.block = true) or none (false)
function shapeSegs(sh, open){ const P = sh.p || [], all = sh.block === true, K = +open + (all ? 2 : 0), C = SHSEG.get(P) || {}; if (C[K]) return C[K]; const L = [];
  P.forEach(([k, d]) => { if ((!all && !SH_BLOCK.test(k)) || (open && k === "door")) return; let st = null, prev = null;
    String(d).replace(/([MLZ])([^MLZ]*)/gi, (m, op, args) => { const v = args.trim().split(/[\s,]+/).filter(Boolean).map(Number), U = op.toUpperCase();
      if (U === "Z"){ if (prev && st && (prev[0] !== st[0] || prev[1] !== st[1])) L.push([prev[0], prev[1], st[0], st[1]]); prev = st; return ""; }
      for (let i = 0; i + 1 < v.length; i += 2){ const q = [v[i], v[i + 1]]; if (U === "M" && i === 0){ st = q; prev = q; } else { if (prev && (prev[0] !== q[0] || prev[1] !== q[1])) L.push([prev[0], prev[1], q[0], q[1]]); prev = q; } }
      return ""; }); });
  C[K] = L; SHSEG.set(P, C); return L; }
// building outlines brought in from a landscape drawing: closed, solid (a camera outside does not see in, one inside not out)
function camSolids(p){ const out = []; (p.shapes || []).forEach(sh => { if (!sh.solid || sh.block === false) return; const kx = sh.w / (sh.w0 || sh.w || 1), ky = sh.h / (sh.h0 || sh.h || 1), cx = sh.w / 2, cy = sh.h / 2, r = num(sh.rot) * Math.PI / 180, c = Math.cos(r), sn = Math.sin(r);
    const T = (x, y) => { x = x * kx - cx; y = y * ky - cy; return [sh.x + cx + x * c - y * sn, sh.y + cy + x * sn + y * c]; };
    sh.p.forEach(([k, d]) => { if (!SH_BLOCK.test(k)) return; String(d).split(/(?=M)/).forEach(part => { if (!/Z\s*$/i.test(part)) return; const v = (part.match(/-?\d*\.?\d+(?:e-?\d+)?/g) || []).map(Number), P = []; for (let i = 0; i + 1 < v.length; i += 2){ const q = T(v[i], v[i + 1]); P.push(q[0], q[1]); } if (P.length >= 6) out.push(P); }); }); });
  return out; }
const inPolyB = (P, x, y) => { let c = false; for (let i = 0, j = P.length - 2; i < P.length; j = i, i += 2){ const xi = P[i], yi = P[i + 1], xj = P[j], yj = P[j + 1]; if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c; } return c; };
// a camera fixed on a building wall drawn as one line: its view starts 15 cm off the wall, on the side it looks at
// (outside for a camera looking out, inside for one looking into the garage), so the wall itself cuts the view
function camOrigin(SOL, x, y, a){ let best = null;
  SOL.forEach(P => { for (let i = 0, j = P.length - 2; i < P.length; j = i, i += 2){ const x1 = P[j], y1 = P[j + 1], ex = P[i] - x1, ey = P[i + 1] - y1, L2 = ex * ex + ey * ey; if (L2 < 1e-9) continue; const u = clamp(((x - x1) * ex + (y - y1) * ey) / L2, 0, 1), qx = x1 + ex * u, qy = y1 + ey * u, dd = Math.hypot(x - qx, y - qy);
    if (dd < .6 && (!best || dd < best.d)){ const L = Math.sqrt(L2); let nx = ey / L, ny = -ex / L; if (inPolyB(P, qx + nx * .02, qy + ny * .02)){ nx = -nx; ny = -ny; } best = {d:dd, qx, qy, nx, ny, P}; } } });
  if (!best) return {x, y}; const into = inPolyB(best.P, x + Math.cos(a), y + Math.sin(a)), k = into ? -.15 : .15;
  return {x:best.qx + best.nx * k, y:best.qy + best.ny * k}; }
function camObstacles(p){ const S = [], vec = !!(p.vec && (p.shapes || []).length);
  const push = (x1, y1, x2, y2, ext = 0) => { if (ext){ const L = Math.hypot(x2 - x1, y2 - y1) || 1, ex = (x2 - x1) / L * ext, ey = (y2 - y1) / L * ext; x1 -= ex; y1 -= ey; x2 += ex; y2 += ey; } S.push([x1, y1, x2, y2]); };
  if (vec) (p.shapes || []).forEach(sh => { const kx = sh.w / (sh.w0 || sh.w || 1), ky = sh.h / (sh.h0 || sh.h || 1), cx = sh.w / 2, cy = sh.h / 2, r = num(sh.rot) * Math.PI / 180, c = Math.cos(r), sn = Math.sin(r);
    const T = (x, y) => { x = x * kx - cx; y = y * ky - cy; return [sh.x + cx + x * c - y * sn, sh.y + cy + x * sn + y * c]; };
    shapeSegs(sh, !!sh.open).forEach(g => { const a = T(g[0], g[1]), b = T(g[2], g[3]); push(a[0], a[1], b[0], b[1]); }); });
  (p.walls || []).forEach(w => { if (w.low || w.kind === "survey" || (w.kind === "door" && w.open) || (vec && w.src)) return;
    const n = Math.abs(num(w.bend, 0)) > 1 ? 8 : 1; let q = DRAW.wallPt(w, 0);
    for (let i = 1; i <= n; i++){ const r = DRAW.wallPt(w, i / n); push(num(q.x), num(q.y), num(r.x), num(r.y), .3); q = r; } });
  (p.items || []).filter(it => it.type === "boundary" && Array.isArray(it.pts)).forEach(it => { const P = it.pts, k = Math.floor(P.length / 2); for (let i = 0; i < k; i++){ const j = (i + 1) % k; push(P[2 * i], P[2 * i + 1], P[2 * j], P[2 * j + 1]); } });
  return S; }
// obstacles sorted into 1 m cells, so a ray only tests what lies along it (a drawing has thousands of line pieces)
function camGrid(S){ const m = new Map();
  S.forEach((g, i) => { const x0 = Math.floor(Math.min(g[0], g[2]) - .3), x1 = Math.floor(Math.max(g[0], g[2]) + .3), y0 = Math.floor(Math.min(g[1], g[3]) - .3), y1 = Math.floor(Math.max(g[1], g[3]) + .3);
    for (let X = x0; X <= x1; X++) for (let Y = y0; Y <= y1; Y++){ const k = X * 100003 + Y; let a = m.get(k); if (!a) m.set(k, a = []); a.push(g); } });
  return m; }
function rayGrid(G, x, y, dx, dy, R){ let best = R; const seen = new Set();
  for (let t = 0; t <= best + .5; t += .4){ const a = G.get(Math.floor(x + dx * t) * 100003 + Math.floor(y + dy * t)); if (!a) continue;
    for (const g of a){ if (seen.has(g)) continue; seen.add(g); const ex = g[2] - g[0], ey = g[3] - g[1], den = dx * ey - dy * ex; if (Math.abs(den) < 1e-9) continue;
      const q = ((g[0] - x) * ey - (g[1] - y) * ex) / den, u = ((g[0] - x) * dy - (g[1] - y) * dx) / den; if (q > .12 && q < best && u >= -1e-6 && u <= 1 + 1e-6) best = q; } }
  return best; }
function planSvg(b, f, opts = {}){
  const p = fixFloorPlan(f), s = opts.s || scaleFor(f), W = p.wm * s, H = p.hm * s, sel = opts.print ? null : UI.sel, S = st(), HO = opts.print ? null : host();
  const isSel = (type, id) => sel && sel.type === type && sel.id === id;
  const E = extOf(b, f, opts.print), es = E * s, TW = W + 2 * es, TH = H + 2 * es;
  let h = "";
  if (S.grid && !opts.print && E){ let g = ""; for (let x = -E; x <= p.wm + E; x++) g += `M${x * s} ${-es}V${H + es}`; for (let y = -E; y <= p.hm + E; y++) g += `M${-es} ${y * s}H${W + es}`; h += `<path d="${g}" stroke="#e3e7ee" stroke-width="1"/>`; }
  h += `<rect class="bfl" x="0" y="0" width="${W}" height="${H}" fill="#fff" stroke="#1d2433" stroke-width="2.5"/>`;
  const vec = !!p.vec, imgOp = vec ? num(p.bgop, 0) : num(p.op, 60);
  if (p.img && assetURL(p.img) && imgOp > 0) h += `<image href="${assetURL(p.img)}" x="0" y="0" width="${W}" height="${H}" preserveAspectRatio="none" opacity="${imgOp / 100}" pointer-events="none"/>`;
  if (S.grid && !opts.print){ let g = ""; for (let x = 1; x < p.wm; x++) g += `M${x * s} 0V${H}`; for (let y = 1; y < p.hm; y++) g += `M0 ${y * s}H${W}`; h += `<path d="${g}" stroke="#e8ebf0" stroke-width="1"/>`; }
  const drawn = p.img && assetURL(p.img), site = isSite(f), fo = site ? ".55" : vec ? ".3" : drawn ? (num(p.op, 60) >= 90 ? ".3" : ".5") : ".82", quiet = !site && (drawn || vec) && !S.outlines;   // places on the site plan stay outlined
  // boundaries (yard, plot, house edge) under everything
  p.items.filter(it => it.type === "boundary").forEach(it => { h += DRAW.boundSvg(it, s, isSel("bitem", it.id), opts.print); });
  let labs = "";
  geoRooms(b, f).forEach(r => { normRoom(r); const g = r.geo, [bg, fg] = RT[r.type], x = g.x * s, y = g.y * s, w = g.w * s, hh = g.h * s, on = isSel("room", r.id);
    const miss = RK.filter(k => reqOf(r, k) > placedIn(b, r, k)), sum = RK.filter(k => reqOf(r, k)).map(k => `${RK_SHORT[k]} ${placedIn(b, r, k)}/${reqOf(r, k)}`).join(" · ");
    const shape = Array.isArray(g.poly) && g.poly.length >= 6 ? `<polygon points="${polyPts(g, s)}"` : `<rect x="${x}" y="${y}" width="${w}" height="${hh}"`;
    h += `<g class="brm" data-room="${r.id}">${shape} fill="${bg}" fill-opacity="${fo}" stroke="${fg}" stroke-width="${on ? 3 : drawn ? 1 : 1.6}"${quiet && !on ? ' stroke-opacity="0"' : ""}${r.type === "corridor" || drawn || vec ? ' stroke-dasharray="6 4"' : ""}/></g>`;
    // names on a layer of their own above every room and drawing piece, so they can always be grabbed
    labs += `<g class="brl">${labHit(r, g, s, x, y)}${g.lx !== undefined ? `<text class="rlab" data-rlab="${r.id}" x="${(g.x + g.lx * (g.pw ? g.w / g.pw : 1)) * s}" y="${(g.y + g.ly * (g.ph ? g.h / g.ph : 1)) * s}" text-anchor="middle" font-size="${clamp(s * .38, 9, 13)}" font-weight="700" fill="${fg}" stroke="#fff" stroke-width="3" paint-order="stroke">${esc(r.name)}</text>${w > 60 ? `<text data-rlab="${r.id}" x="${(g.x + g.lx * (g.pw ? g.w / g.pw : 1)) * s}" y="${(g.y + g.ly * (g.ph ? g.h / g.ph : 1)) * s + 12}" text-anchor="middle" font-size="9" fill="#4b5262" stroke="#fff" stroke-width="2.5" paint-order="stroke">${esc(area(r) + " m²" + (g.est ? " ≈" : "") + (num(r.users) ? " · 👤" + num(r.users) : ""))}</text>` : ""}`
      : `<text class="rlab" data-rlab="${r.id}" x="${x + 6}" y="${y + 15}" font-size="${clamp(s * .45, 10, 14)}" font-weight="700" fill="${fg}">${esc(r.name)}</text>
      ${w > 70 ? `<text data-rlab="${r.id}" x="${x + 6}" y="${y + 28}" font-size="9.5" fill="#4b5262">${esc(area(r) + " m²" + (num(r.users) ? " · 👤" + num(r.users) : ""))}</text>` : ""}`}
      ${sum && w > 90 ? `<text x="${x + 6}" y="${y + hh - 6}" pointer-events="none" font-size="9" fill="${miss.length ? "#b3262f" : "#1f7a35"}">${esc(sum)}</text>` : ""}</g>`;
    if (on && !opts.print && !(HO && HO.lockRooms)) h += `<rect class="bres" data-res="room:${r.id}" x="${x + w - 7}" y="${y + hh - 7}" width="14" height="14" rx="3"/>`; });
  // the floor below, faint, where it stands under this one (floors lined up by «Line up floors» / a DXF import)
  if (S.ghost && !opts.print && !isSite(f)){ const k = b.floors.indexOf(f), fb = k > 0 ? b.floors[k - 1] : null, W2 = fb && fb.plan ? siteWalls(fb.plan) : null;
    if (W2){ const ddx = num(fb.plan.ox, 0) - num(p.ox, 0), ddy = num(fb.plan.oy, 0) - num(p.oy, 0); let d = ""; W2.S.forEach(q => { d += `M${((q[0] + ddx) * s).toFixed(1)} ${((q[1] + ddy) * s).toFixed(1)}L${((q[2] + ddx) * s).toFixed(1)} ${((q[3] + ddy) * s).toFixed(1)}`; });
      h += `<path d="${d}" stroke="#7c3aed" stroke-opacity=".45" stroke-width="2" fill="none" stroke-dasharray="6 3" pointer-events="none"/><text x="6" y="${(p.hm * s - 8).toFixed(0)}" font-size="11" fill="#7c3aed" font-weight="700">↧ ${esc(fb.name)}</text>`; } }
  if (vec) h += DRAW.shapesSvg(p, s, sel, opts.print);
  if (!drawn || vec) h += DRAW.wallsSvg(p, s, sel, opts.print);
  h += labs;
  const shSel = sel && sel.type === "bshape" && p.shapes && p.shapes.find(o => o.id === sel.id);
  if (shSel && !opts.print){ const o = shSel, cx = (o.x + o.w / 2) * s, cy = (o.y + o.h / 2) * s; h += `<g transform="rotate(${o.rot || 0} ${cx} ${cy})">${rotHandle("bshape:" + o.id, cx, o.y * s)}<rect class="bres" data-res="bshape:${o.id}" x="${(o.x + o.w) * s - 6}" y="${(o.y + o.h) * s - 6}" width="12" height="12" rx="3"/></g>`; }
  p.items.filter(it => it.type !== "boundary").forEach(it => { const x = it.x * s, y = it.y * s, w = it.w * s, hh = it.h * s, on = isSel("bitem", it.id), c = "#3a4552";
    let g = "";
    if (it.type === "stairs"){ g = `<rect width="${w}" height="${hh}" fill="#fff" stroke="${c}" stroke-width="1.5"/>`; const n = Math.max(3, Math.round(it.h / .3)); for (let i = 1; i < n; i++) g += `<line x1="0" y1="${hh * i / n}" x2="${w}" y2="${hh * i / n}" stroke="${c}" stroke-width=".8"/>`; g += `<path d="M${w / 2} ${hh - 4}V6M${w / 2 - 4} 12L${w / 2} 5L${w / 2 + 4} 12" stroke="${c}" fill="none" stroke-width="1.2"/>`; }
    else if (it.type === "elevator") g = `<rect width="${w}" height="${hh}" fill="#fff" stroke="${c}" stroke-width="1.8"/><path d="M0 0L${w} ${hh}M${w} 0L0 ${hh}" stroke="${c}" stroke-width="1"/>`;
    else if (it.type === "shaft") g = `<rect width="${w}" height="${hh}" fill="#d9dde6" stroke="${c}" stroke-width="1.2"/><path d="M0 ${hh}L${w} 0" stroke="${c}"/>`;
    else if (it.type === "door") g = `<rect width="${w}" height="${Math.max(3, hh)}" fill="#fff" stroke="#b0702a" stroke-width="1.5"/><path d="M0 0A${w} ${w} 0 0 1 ${w} ${w}" fill="none" stroke="#b0702a" stroke-width=".8" stroke-dasharray="3 2"/>`;
    else if (it.type === "window") g = `<rect width="${w}" height="${Math.max(3, hh)}" fill="#d6ecff" stroke="#3b82c4" stroke-width="1.5"/>`;
    else if (it.type === "column") g = `<rect width="${w}" height="${hh}" fill="#59607a"/>`;
    else if (it.type === "yard") g = `<rect width="${w}" height="${hh}" fill="#e6f6ea" fill-opacity=".35" stroke="#2e9d57" stroke-width="2.5" stroke-dasharray="10 5"/><text x="6" y="16" font-size="12" font-weight="700" fill="#2e9d57">${esc(it.text || t("bi_yard"))}</text>`;
    else if (DRAW.isSym(it.type)) g = DRAW.symSvg(it, w, hh);
    else g = `<text x="2" y="${Math.min(hh, 16) - 3}" font-size="${clamp(it.size || 12, 8, 30)}" font-weight="700" fill="#1d2433">${esc(it.text || t("bd_label"))}</text>`;
    h += `<g class="bit" data-bitem="${it.id}" transform="translate(${x} ${y})${it.rot ? ` rotate(${it.rot} ${w / 2} ${hh / 2})` : ""}">${g}${on && !opts.print ? `<rect width="${w}" height="${Math.max(hh, 4)}" fill="none" stroke="#ffb703" stroke-width="2.5" stroke-dasharray="5 3"/>` : ""}</g>`;
    if (on && !opts.print) h += `<g transform="rotate(${it.rot || 0} ${x + w / 2} ${y + hh / 2})">${rotHandle("bitem:" + it.id, x + w / 2, y)}${it.type !== "label" ? `<rect class="bres" data-res="bitem:${it.id}" x="${x + w - 6}" y="${y + Math.max(hh, 4) - 6}" width="12" height="12" rx="3"/>` : ""}</g>`; });
  b.racks.filter(r => r.floor === f.id && r.pos).forEach(r => { const x = r.pos.x * s, y = r.pos.y * s, on = isSel("rack", r.id);
    h += `<g class="bdev" data-brack="${r.id}" transform="translate(${x} ${y})"><rect x="-10" y="-13" width="20" height="26" rx="2" fill="#232a33" stroke="${on ? "#ffb703" : "#fff"}" stroke-width="${on ? 3 : 1.2}"/><path d="M-6 -8h12M-6 -3h12M-6 2h12M-6 7h12" stroke="#7fd1ff" stroke-width="1.6"/>
      ${S.labels ? `<text y="24" font-size="9" font-weight="700" text-anchor="middle" fill="#1d2433" stroke="#fff" stroke-width="2.5" paint-order="stroke">${esc(r.name)}</text>` : ""}</g>`; });
  const camsOn = (HO && HO.cams) || (opts.print && opts.cams) || S.cones, OBS = camsOn ? camGrid(camObstacles(p)) : null, SOL = camsOn ? camSolids(p) : [];
  if (camsOn) b.devices.filter(d => d.kind === "camera" && devFloor(b, d) === f.id && posOf(d)).forEach(d => { const P0 = posOf(d), C = window.CCTV && CCTV.camCalc ? CCTV.camCalc(b, d) : {}, fov = clamp(num(C.fov, 90), 10, 360), Rm = clamp(num(C.dori && C.dori[1], 20), 3, 60), R = Rm * s, a = num(d.camera && d.camera.dir, 0) * Math.PI / 180, h2 = fov * Math.PI / 360;
    const x = P0.x * s, y = P0.y * s, on = isSel("dev", d.id), O = SOL.length ? camOrigin(SOL, P0.x, P0.y, a) : P0;
    // the view stops at walls, retaining walls and the plot boundary: rays every ~1° (shorter where something is in the way)
    const n = Math.max(24, Math.round(fov * 2)), pt = [];
    for (let i = 0; i <= n; i++){ const t = a - h2 + 2 * h2 * i / n, dx = Math.cos(t), dy = Math.sin(t), L = rayGrid(OBS, O.x, O.y, dx, dy, Rm); pt.push(`${((O.x + dx * L) * s).toFixed(1)} ${((O.y + dy * L) * s).toFixed(1)}`); }
    h += `<path d="${fov >= 359 ? "M" + pt.join("L") : `M${x} ${y}L` + pt.join("L")}Z" fill="rgba(255,183,3,${on ? .26 : .15})" stroke="#e0a400" stroke-width="${on ? 1.6 : 1}" stroke-linejoin="round" pointer-events="none"/>`;
    if (on && !opts.print){ const hx = x + R * .55 * Math.cos(a), hy = y + R * .55 * Math.sin(a); h += `<line x1="${x}" y1="${y}" x2="${hx}" y2="${hy}" stroke="#e0a400" stroke-width="1.5" stroke-dasharray="4 3" pointer-events="none"/><circle class="camrot" data-camrot="${d.id}" cx="${hx}" cy="${hy}" r="8" fill="#ffb703" stroke="#7a5600" stroke-width="1.5"><title>${esc(t("camRotate"))}</title></circle>`; } });
  b.devices.filter(d => devFloor(b, d) === f.id && posOf(d)).forEach(d => { const P0 = posOf(d), x = P0.x * s, y = P0.y * s, on = isSel("dev", d.id) || UI.multi.has("dev:" + d.id), pl = d.status === "planned", fade = HO && HO.kinds && !HO.kinds.includes(d.kind);
    h += `<g class="bdev${fade ? " fade" : ""}" data-bdev="${d.id}" transform="translate(${x} ${y})"${fade ? ' opacity=".35"' : ""}><circle r="11" fill="#fff" stroke="${on ? "#ffb703" : pl ? "#5b7fc4" : "#1d2433"}" stroke-width="${on ? 3 : pl ? 1.6 : 1.1}"${pl ? ' stroke-dasharray="3 2"' : ""}/><g transform="translate(-9 -9) scale(.375)">${ICO[devIcon(d)] || ICO.box}</g>
      ${S.labels ? `<text y="21" font-size="8.5" font-weight="700" text-anchor="middle" fill="#1d2433" stroke="#fff" stroke-width="2.5" paint-order="stroke">${esc(d.name)}</text>` : ""}</g>`; });
  const m = [1,2,5,10,20].find(v => v * s >= 50) || 20;
  h = `<g transform="translate(${es} ${es})">${h}</g>`;
  h += `<g transform="translate(${TW - m * s - 12} ${TH - 12})" pointer-events="none"><rect x="-4" y="-14" width="${m * s + 8}" height="18" fill="#fff" opacity=".85" rx="3"/><path d="M0 0V-5M0 0H${m * s}V-5" stroke="#1d2433" fill="none" stroke-width="1.5"/><text x="${m * s / 2}" y="-5" font-size="9.5" font-weight="700" text-anchor="middle">${m} m</text></g>`;
  return `<svg class="bplan" data-bfloor="${f.id}" data-e="${E}" data-fit="${es - 10} ${es - 10} ${W + 20} ${H + 20}" data-anchor="${es} ${es}" viewBox="0 0 ${TW} ${TH}" width="${TW}" height="${TH}" font-family="Barlow,Segoe UI,Arial,sans-serif">${opts.print ? "" : `<rect x="0" y="0" width="${TW}" height="${TH}" fill="#f6f7f9"/>`}${h}</svg>`;
}

/* ---------- plan page ---------- */
function crumbs(b, f){ return `<div class="bcrumb"><span>🏢 <b>${esc(b.name)}</b></span>${f ? `<span>›</span><span>${isSite(f) ? "🌳" : "🏬"} <b>${esc(f.name)}</b> <small class="muted">${esc(r1(f.plan.wm) + " × " + r1(f.plan.hm) + " m · " + roomsOf(b, f).length + " " + t("bd_roomsN"))}</small></span>` : ""}</div>`; }
function floorChips(b, f){ return `<div class="bfloors">${b.floors.slice().reverse().map(x => `<button class="bfchip${f && x.id === f.id ? " on" : ""}" data-bfl="${x.id}">🏬 ${esc(x.name)} <small>${roomsOf(b, x).length}</small></button>`).join("")}<button class="bfchip site${isSite(f) ? " on" : ""}" data-bfl="${OUT_FLOOR}" title="${esc(t("sitePlanH"))}">🌳 ${esc(b.site && b.site.name || t("sitePlan"))} <small>${roomsOf(b, {id:OUT_FLOOR}).length}</small></button><button class="bfchip add" data-ba="addFloor">＋ ${esc(t("floorNew"))}</button></div>`; }
function planView(){
  const b = B(), f = curFloor(b);
  if (!f) return `<div class="empty"><h3>${esc(t("bd_emptyT"))}</h3><p>${esc(t("bd_empty"))}</p><div class="btns" style="justify-content:center"><button class="btn pri" data-ba="wizard">🧭 ${esc(t("bd_wizard"))}</button><button class="btn pri" data-ba="dxf">📐 ${esc(t("dx_btn"))}</button><button class="btn" data-ba="addFloor">＋ ${esc(t("floorNew"))}</button></div></div>`;
  const dups = dupRooms(b, f);
  return `${crumbs(b, f)}${floorChips(b, f)}${warnBox(bWarnings(b, f))}${dups.length ? `<div class="lbox row">🧩 ${esc(t("dw_dupFix",{n:dups.length}))}<span class="grow"></span><button class="btn small pri" data-ba="mergeDup">${esc(t("dw_dupBtn"))}</button></div>` : ""}${zpWrap(UI.app + ":" + f.id, planSvg(b, f))}<p class="dghint">${esc(place ? t("bd_hintPlace") : t("bd_hint"))}</p>`;
}
function palette(){
  const b = B(), f = curFloor(b); if (!f) return "";
  const P = (key, label, ic) => `<div class="pitem bpi${place === key ? " on" : ""}" draggable="true" data-bplace="${key}" title="${esc(label)}">${ic}<span>${esc(label)}</span></div>`;
  const svgI = ic => `<svg viewBox="0 0 48 48">${ICO[ic] || ICO.box}</svg>`;
  const HO = host(), KS = HO && HO.kinds ? HO.kinds.filter(k => KINDS[k]) : DEVK;
  const unplaced = b.devices.filter(d => (devFloor(b, d) === f.id || (HO && HO.kinds && !devFloor(b, d))) && !posOf(d) && KS.includes(d.kind) && !d.rack);
  if (HO && HO.kinds) return `<div class="psec"><h4>${esc(t("bd_devs"))}</h4><div class="pgrid">${expandKinds(KS).map(k => P("dev:" + k, variantName(k), svgI(variantIcon(k)))).join("")}${ukBtn("cctvplan")}</div><p class="muted small">${esc(t("camPlanHint"))}</p></div>
    ${unplaced.length ? `<div class="psec"><h4>${esc(t("bd_unplaced"))} <span class="cnt">${unplaced.length}</span></h4><div class="ulist">${unplaced.slice(0, 80).map(d => `<button class="ub${place === "put:" + d.id ? " on" : ""}" data-bput="${d.id}">${esc(devLabel(d))}${d.room ? ` <small class="muted">${esc(roomName(b, d.room))}</small>` : ""}</button>`).join("")}</div></div>` : ""}
    <div class="psec"><h4>${esc(t("palView"))}</h4><label class="chk"><input type="checkbox" data-bopt="labels"${st().labels ? " checked" : ""}> ${esc(t("bd_labels"))}</label><label class="chk"><input type="checkbox" data-bopt="grid"${st().grid ? " checked" : ""}> ${esc(t("bd_grid"))}</label></div>`;
  return `<div class="psec"><h4>${esc(t("bd_struct"))}</h4><div class="pgrid">
      ${P("room:office", t("bd_room"), `<svg viewBox="0 0 48 48"><rect x="6" y="10" width="36" height="28" fill="#e8f0ff" stroke="#2f5fc4" stroke-width="3"/></svg>`)}
      ${P("room:corridor", t("rt_corridor"), `<svg viewBox="0 0 48 48"><rect x="4" y="18" width="40" height="12" fill="#f2f3f5" stroke="#7b8494" stroke-width="2.5" stroke-dasharray="5 3"/></svg>`)}
      ${P("room:server", t("rt_server"), `<svg viewBox="0 0 48 48"><rect x="6" y="10" width="36" height="28" fill="#ffe9e6" stroke="#b3262f" stroke-width="3"/><rect x="18" y="16" width="12" height="16" fill="#232a33"/></svg>`)}
      ${P("item:stairs", t("bi_stairs"), `<svg viewBox="0 0 48 48"><rect x="12" y="6" width="24" height="36" fill="#fff" stroke="#3a4552" stroke-width="2"/><path d="M12 14h24M12 22h24M12 30h24M12 38h24" stroke="#3a4552"/></svg>`)}
      ${P("item:elevator", t("bi_elevator"), `<svg viewBox="0 0 48 48"><rect x="10" y="10" width="28" height="28" fill="#fff" stroke="#3a4552" stroke-width="2.5"/><path d="M10 10L38 38M38 10L10 38" stroke="#3a4552"/></svg>`)}
      ${P("item:door", t("bi_door"), `<svg viewBox="0 0 48 48"><path d="M10 34h28" stroke="#b0702a" stroke-width="4"/><path d="M10 34A26 26 0 0 1 36 8" fill="none" stroke="#b0702a" stroke-dasharray="3 2"/></svg>`)}
      ${P("item:window", t("bi_window"), `<svg viewBox="0 0 48 48"><rect x="6" y="20" width="36" height="8" fill="#d6ecff" stroke="#3b82c4" stroke-width="2.5"/></svg>`)}
      ${P("item:column", t("bi_column"), `<svg viewBox="0 0 48 48"><rect x="16" y="16" width="16" height="16" fill="#59607a"/></svg>`)}
      ${P("item:shaft", t("bi_shaft"), `<svg viewBox="0 0 48 48"><rect x="12" y="12" width="24" height="24" fill="#d9dde6" stroke="#3a4552" stroke-width="2"/><path d="M12 36L36 12" stroke="#3a4552" stroke-width="2"/></svg>`)}
      ${P("item:yard", t("bi_yard"), `<svg viewBox="0 0 48 48"><rect x="4" y="8" width="40" height="32" fill="#e6f6ea" stroke="#2e9d57" stroke-width="2.5" stroke-dasharray="6 3"/><path d="M14 30c2-6 6-6 8 0M28 22c2-6 6-6 8 0" stroke="#2e9d57" fill="none" stroke-width="2"/></svg>`)}
      ${P("item:label", t("bd_label"), `<svg viewBox="0 0 48 48">${ICO.text || ""}</svg>`)}
    </div></div>
    <div class="psec"><h4>${esc(t("dw_secWalls"))}</h4><div class="pgrid">
      ${P("tool:wall", t("dw_wall"), `<svg viewBox="0 0 48 48"><path d="M6 38L42 10" stroke="#3a3f4b" stroke-width="8"/><path d="M6 38L42 10" stroke="#d9dde4" stroke-width="4"/></svg>`)}
      ${P("tool:wallc", t("dw_wallC"), `<svg viewBox="0 0 48 48"><path d="M6 38A24 24 0 0 1 42 12" stroke="#3a3f4b" stroke-width="8" fill="none"/><path d="M6 38A24 24 0 0 1 42 12" stroke="#d9dde4" stroke-width="4" fill="none"/></svg>`)}
      ${P("tool:bound", t("dw_bound"), `<svg viewBox="0 0 48 48"><path d="M6 14L24 6L42 16L38 40L10 36Z" fill="#e6f6ea" stroke="#2e9d57" stroke-width="2.5" stroke-dasharray="5 3"/></svg>`)}
      ${P("tool:house", t("dw_house"), `<svg viewBox="0 0 48 48"><path d="M8 12H30V22H40V38H8Z" fill="none" stroke="#111722" stroke-width="3.5"/></svg>`)}
    </div><p class="muted small">${esc(t("dw_wallHint"))}</p></div>
    ${DRAW.GROUPS.map(gr => `<details class="psec pdet"${(st().pdet || {})[gr] ? " open" : ""} data-bpdet="${gr}"><summary><h4>${esc(t("dw_grp_" + gr))}</h4></summary><div class="pgrid">${Object.keys(DRAW.SYM).filter(k => DRAW.SYM[k][2] === gr).map(k => P("item:" + k, itemName(k), DRAW.icon(k))).join("")}</div></details>`).join("")}
    <div class="psec"><h4>${esc(t("bd_devs"))}</h4><div class="pgrid">${expandKinds(DEVK).map(k => P("dev:" + k, variantName(k), svgI(variantIcon(k)))).join("")}${ukBtn("building")}${P("rack", t("k_rack") === "k_rack" ? "Rack" : t("k_rack"), svgI("rack"))}</div></div>
    ${unplaced.length ? `<div class="psec"><h4>${esc(t("bd_unplaced"))} <span class="cnt">${unplaced.length}</span></h4><div class="ulist">${unplaced.slice(0, 60).map(d => `<button class="ub${place === "put:" + d.id ? " on" : ""}" data-bput="${d.id}">${esc(devLabel(d))}${d.room ? ` <small class="muted">${esc(roomName(b, d.room))}</small>` : ""}</button>`).join("")}</div></div>` : ""}
    <div class="psec"><h4>${esc(t("palView"))}</h4><label class="chk"><input type="checkbox" data-bopt="labels"${st().labels ? " checked" : ""}> ${esc(t("bd_labels"))}</label><label class="chk"><input type="checkbox" data-bopt="grid"${st().grid ? " checked" : ""}> ${esc(t("bd_grid"))}</label><label class="chk"><input type="checkbox" data-bopt="cones"${st().cones ? " checked" : ""}> ${esc(t("camCones"))}</label>${!isSite(f) && b.floors.indexOf(f) > 0 ? `<label class="chk" title="${esc(t("fa_ghostH"))}"><input type="checkbox" data-bopt="ghost"${st().ghost ? " checked" : ""}> ${esc(t("fa_ghost"))}</label>` : ""}${f.plan.img || f.plan.vec ? `<label class="chk"><input type="checkbox" data-bopt="outlines"${st().outlines ? " checked" : ""}> ${esc(t("dw_outlines"))}</label>` : ""}
      ${f.plan.img || (f.plan.shapes || []).length ? `<label class="chk"><input type="checkbox" data-bvec="1"${f.plan.vec ? " checked" : ""}> ✏ ${esc(t("dw_vec"))}</label>${f.plan.vec ? `<label class="chk" title="${esc(t("dw_moveRfH"))}"><input type="checkbox" data-bmoverf="1"${store.settings.moveRf !== false ? " checked" : ""}> ${esc(t("dw_moveRf"))}</label><p class="muted small">${esc(t("dw_moveRfH"))}</p><label class="fld"><span>${esc(t("dw_bgop"))}: ${num(f.plan.bgop, 0)}%</span><input type="range" min="0" max="100" step="5" value="${num(f.plan.bgop, 0)}" data-bbgop="1"></label>${(f.plan.shapes || []).length ? "" : `<p class="muted small">${esc(t("dw_vecNoPieces"))}</p>`}` : ""}` : ""}
      <button class="btn small wfull" data-ba="wizard">🧭 ${esc(t("bd_wizard"))}</button><button class="btn small wfull" data-ba="dxf">📐 ${esc(t("dx_btn"))}</button>${!isSite(f) && b.floors.length > 1 ? `<button class="btn small wfull" data-ba="alignFloors" title="${esc(t("fa_btnH"))}">⇅ ${esc(t("fa_btn"))}</button>` : ""}${isSite(f) ? `<button class="btn small wfull" data-ba="lndDxf" title="${esc(t("lx_btnH"))}">🌳 ${esc(t("lx_btn"))}</button>` : ""}
      ${isSite(f) && ((f.plan.shapes || []).some(o => o.k === "lnd") || (f.plan.items || []).some(o => o.src === "lnd")) ? `<div class="lbox small"><b>🌳 ${esc(t("lx_moveT"))}</b><p class="muted small">${esc(t("lx_moveH"))}</p>
        ${[[.1, "10 sm"], [1, "1 m"]].map(([d, l]) => `<div class="btns" style="gap:4px;margin:3px 0"><span class="muted small" style="width:38px">${l}</span>${[["←", -d, 0], ["→", d, 0], ["↑", 0, -d], ["↓", 0, d]].map(([a, x, y]) => `<button class="btn small ghost" data-ba="lndMv:${x},${y}">${a}</button>`).join("")}</div>`).join("")}
        <button class="btn small ghost wfull" data-ba="lndDel">🗑 ${esc(t("lx_del"))}</button></div>` : ""}</div>`;
}

/* ---------- structure page: building → floors → rooms ---------- */
function structView(){
  const b = B();
  if (!b.floors.length) return planView();
  const F = b.floors.slice().reverse();
  return `<div class="card"><h3>🏢 ${esc(b.name)}<span class="grow"></span><button class="btn small" data-ba="wizard">🧭 ${esc(t("bd_wizard"))}</button><button class="btn small" data-ba="addFloor">＋ ${esc(t("floorNew"))}</button></h3>
    <p class="muted small">${esc(t("bd_structHint"))}</p>
    <div class="kpis">${[[b.floors.length, t("floors")], [b.rooms.length, t("rooms")], [r1(b.floors.reduce((a, f) => a + num(f.plan.wm) * num(f.plan.hm), 0)) + " m²", t("bd_areaTot")], [b.devices.length, t("devices")]].map(([v, l]) => `<div class="kpi"><b>${esc(v)}</b><span>${esc(l)}</span></div>`).join("")}</div>
    <div class="btree">${F.concat([siteOf(b)]).map(f => { const R = roomsOf(b, f), i = b.floors.indexOf(f), site = isSite(f);
      return `<div class="bfcard${site ? " site" : ""}"><div class="bfhead"><b>${site ? "🌳" : "🏬"}</b><input class="bin" data-bfn="${f.id}" value="${esc(f.name)}"><small class="muted">${esc(r1(f.plan.wm) + " × " + r1(f.plan.hm) + " m · " + R.length + " " + t("bd_roomsN"))}</small><span class="grow"></span>
        <button class="btn small" data-ba="goFloor:${f.id}">🗺 ${esc(t("bd_openPlan"))}</button>${site ? "" : `<button class="btn small" data-ba="fUp:${f.id}"${i === b.floors.length - 1 ? " disabled" : ""} title="${esc(t("bd_up"))}">▲</button><button class="btn small" data-ba="fDown:${f.id}"${i === 0 ? " disabled" : ""} title="${esc(t("bd_down"))}">▼</button>`}<button class="btn small" data-ba="addRoom:${f.id}">＋ ${esc(t("roomNew"))}</button>${site ? "" : `<button class="btn small dan" data-ba="delFloor:${f.id}">🗑</button>`}</div>
        ${R.length ? `<div class="scroll"><table class="t"><tr><th>${esc(t("f_room"))}</th><th>${esc(t("bd_type"))}</th><th>m²</th><th>👤</th>${RK.map(k => `<th class="c" title="${esc(kindName(k))}">${RK_SHORT[k]}</th>`).join("")}<th></th></tr>
          ${R.map(r => { normRoom(r); return `<tr${UI.sel && UI.sel.type === "room" && UI.sel.id === r.id ? ' class="on"' : ""}><td><input data-brn="${r.id}" value="${esc(r.name)}" style="min-width:130px"></td><td><select data-brt="${r.id}">${RTYPES.map(k => opt(k, t("rt_" + k), r.type)).join("")}</select></td><td class="c">${area(r) || "—"}</td><td><input data-bru="${r.id}" type="text" inputmode="numeric" value="${esc(num(r.users) || "")}" style="width:44px"></td>
            ${RK.map(k => { const q = reqOf(r, k), pl = placedIn(b, r, k); return `<td class="c"><div class="breqc"><input class="breq${q && pl < q ? " miss" : q && pl >= q ? " ok" : ""}" data-brq="${r.id}:${k}" type="text" inputmode="numeric" value="${q || ""}" placeholder="0" title="${esc(kindName(k) + ": " + t("bd_placed") + " " + pl + " / " + t("bd_req") + " " + q)}"><small class="${pl ? "" : "z"}" title="${esc(t("bd_placed"))}">${pl ? "📍" + pl : "·"}</small></div></td>`; }).join("")}
            <td class="nw"><button class="btn small" data-ba="selRoom:${r.id}" title="${esc(t("bd_openPlan"))}">🗺</button><button class="btn small dan" data-ba="delRoom:${r.id}">×</button></td></tr>`; }).join("")}</table></div>` : `<p class="muted small">${esc(t("bd_noRooms"))}</p>`}</div>`; }).join("")}</div></div>`;
}
/* ---------- needs page: what is required vs what is placed ---------- */
function reqView(){
  const b = B(); if (!b.rooms.length) return `<div class="empty" data-tp="req"><p>${esc(t("bd_noRooms"))}</p></div>`;
  const tot = {}, totP = {}; RK.forEach(k => { tot[k] = 0; totP[k] = 0; });
  const rows = b.floors.slice().reverse().concat(b.rooms.some(r => r.floor === OUT_FLOOR) ? [siteOf(b)] : []).map(f => { const R = roomsOf(b, f); if (!R.length) return "";
    return `<tr class="tot"><td colspan="${RK.length + 2}">${isSite(f) ? "🌳" : "🏬"} ${esc(f.name)}</td></tr>` + R.map(r => `<tr><td>${esc(r.name)}</td><td class="small">${esc(t("rt_" + normRoom(r).type))}</td>${RK.map(k => { const q = reqOf(r, k), pl = placedIn(b, r, k); tot[k] += q; totP[k] += pl; return `<td class="c ${q && pl < q ? "bad" : q ? "ok" : ""}">${q || pl ? `${pl}/${q}` : ""}</td>`; }).join("")}</tr>`).join(""); }).join("");
  const missing = RK.reduce((a, k) => a + Math.max(0, tot[k] - totP[k]), 0);
  return `<div class="card"><h3 data-tp="req">📋 ${esc(t("bd_reqT"))}<span class="grow"></span>${missing ? `<button class="btn pri small" data-ba="createAll">＋ ${esc(t("bd_createAll",{n:missing}))}</button>` : ""}<button class="btn small" data-ba="reqCsv">⤓ CSV</button></h3><p class="muted small">${esc(t("bd_reqHint"))}</p>
    <div class="scroll"><table class="t"><tr><th>${esc(t("f_room"))}</th><th>${esc(t("bd_type"))}</th>${RK.map(k => `<th class="c" title="${esc(kindName(k))}">${RK_SHORT[k]}</th>`).join("")}</tr>${rows}
    <tr class="tot"><td colspan="2">${esc(t("total"))}</td>${RK.map(k => `<td class="c">${totP[k]}/${tot[k]}</td>`).join("")}</tr></table></div>
    <p class="muted small">${RK.map(k => `${RK_SHORT[k]} = ${kindName(k)}`).join(" · ")}</p></div>`;
}
// the site plan is printed when it holds something (a drawing, rooms, items or placed devices)
function siteUsed(b){ const s = b.site; if (!s || !s.plan) return false; const p = s.plan;
  return !!(p.img || (p.items || []).length || (p.walls || []).length || (p.shapes || []).length || b.rooms.some(r => r.floor === OUT_FLOOR && r.geo) || b.devices.some(d => devFloor(b, d) === OUT_FLOOR && posOf(d))); }
// the site plan as a page of its own (Summary and CCTV documents); cams: camera view cones on it
function sitePage(b, cams){ const f = siteOf(b); return `<div style="page-break-before:always"></div><h3>🌳 ${esc(f.name)} <small class="muted">${esc(r1(f.plan.wm) + " × " + r1(f.plan.hm) + " m")}</small></h3><div style="border:1px solid #c7d1e6">${planSvg(b, f, {print:true, cams, s:clamp(1100 / Math.max(4, num(f.plan.wm, 40)), 4, 60)}).replace(/width="[\d.]+" height="[\d.]+" font/, 'width="100%" font')}</div>`; }
function docBody(b){
  return b.floors.slice().reverse().concat(siteUsed(b) ? [siteOf(b)] : []).map(f => `<h3>${isSite(f) ? "🌳" : "🏬"} ${esc(f.name)} <small class="muted">${esc(r1(f.plan.wm) + " × " + r1(f.plan.hm) + " m")}</small></h3><div style="border:1px solid #c7d1e6">${planSvg(b, f, {print:true, s:clamp(1100 / Math.max(4, num(f.plan.wm, 40)), 4, 60)}).replace(/width="[\d.]+" height="[\d.]+" font/, 'width="100%" font')}</div>`).join("")
    + `<h3>${esc(t("bd_reqT"))}</h3>` + reqView().replace(/<button[^>]*>.*?<\/button>/g, "");
}
// the same room twice on a floor: an estimated box with the name of an outlined room («TEKNİK ODA 1» over «TEKNİK ODA»)
function dupRooms(b, f){ const R = roomsOf(b, f).filter(r => r.geo), base = n => nrm(n).replace(/\s*\(?\d+\)?$/, "").trim(), out = [];
  const ov = (a, c) => { const x = Math.max(0, Math.min(a.x + a.w, c.x + c.w) - Math.max(a.x, c.x)), y = Math.max(0, Math.min(a.y + a.h, c.y + c.h) - Math.max(a.y, c.y)); return x * y / Math.max(.01, Math.min(a.w * a.h, c.w * c.h)); };
  R.filter(r => r.geo.est).forEach(r => { const tw = R.find(o => o !== r && !o.geo.est && base(o.name) === base(r.name) && ov(o.geo, r.geo) > .5); if (tw) out.push([r, tw]); });
  return out; }
function bWarnings(b, f){
  const W = [], R = roomsOf(b, f), miss = R.filter(r => RK.some(k => reqOf(r, k) > placedIn(b, r, k)));
  if (miss.length) W.push(["info", t("bd_wMiss",{n:miss.length, r:miss.slice(0, 4).map(r => r.name).join(", ") + (miss.length > 4 ? " …" : "")})]);
  const est = R.filter(r => r.geo && r.geo.est); if (est.length) W.push(["info", t("dx_wEst",{n:est.length, r:est.slice(0, 5).map(r => r.name).join(", ") + (est.length > 5 ? " …" : "")}), est[0].id]);
  if (LINK_FLOOR.test(String(f.name).trim())) W.push(["", t("bd_wLinkFloor",{f:f.name})]);
  const nogeo = R.filter(r => !r.geo); if (nogeo.length) W.push(["info", t("bd_wNoGeo",{n:nogeo.length})]);
  dupRooms(b, f).forEach(([r, tw]) => W.push(["", t("dw_wDupRoom",{a:r.name, b:tw.name}), r.id]));
  const out = R.filter(r => r.geo && (r.geo.x + r.geo.w > f.plan.wm + .01 || r.geo.y + r.geo.h > f.plan.hm + .01 || r.geo.x < 0 || r.geo.y < 0)); if (out.length) W.push(["", t("bd_wOut",{r:out.map(r => r.name).join(", ")}), out[0].id]);
  return W;
}

/* ---------- drawer ---------- */
// free angle: a number (degrees) with quick buttons
const rotFld = (path, v, label) => `<label class="fld"><span>${esc(label || t("bd_rot"))} (°)</span><span class="rotf"><input data-f="${path}" type="text" inputmode="decimal" value="${esc(r1(num(v, 0)))}">${[0, 45, 90, 180, 270].map(a => `<button type="button" class="btn small ghost" data-brotset="${path}:${a}">${a}°</button>`).join("")}</span></label>`;
function drawer(tab){
  const b = B(), s = UI.sel; if (!s) return "";
  if (s.type === "dev"){ const d = devById(b, s.id); return d ? deviceEditor(b, d, {btns:posOf(d) ? `<button class="btn" data-dr="bUnplace">⤴ ${esc(t("removeFromView"))}</button>` : ""}) : ""; }
  if (s.type === "link"){ const l = linkById(b, s.id); return l ? linkEditor(b, l) : ""; }
  const head = (title, sub) => `<div class="dhead"><div><h3>${esc(title)}</h3><div class="muted small">${esc(sub)}</div></div><button class="x" data-dr="close">×</button></div>`;
  if (s.type === "room"){ const r = roomById(b, s.id); if (!r) return ""; normRoom(r); const f = planFloor(b, r.floor), g = r.geo;
    return `${head(r.name, (f ? f.name + " · " : "") + (g ? area(r) + " m²" : t("bd_noGeo")))}
      <label class="fld"><span>${esc(t("f_name"))}</span><input data-f="r.name" value="${esc(r.name)}"></label>
      <div class="two"><label class="fld"><span>${esc(t("bd_type"))}</span><select data-f="r.type">${RTYPES.map(k => opt(k, t("rt_" + k), r.type)).join("")}</select></label><label class="fld"><span>${esc(t("f_users"))}</span><input data-f="r.users" type="text" inputmode="numeric" value="${esc(num(r.users))}"></label></div>
      <label class="fld"><span>${esc(t("f_floor"))}</span><select data-f="r.floor">${b.floors.map(x => opt(x.id, x.name, r.floor)).join("")}${opt(OUT_FLOOR, "🌳 " + t("flOut"), r.floor)}</select></label>
      ${g ? `<div class="two">${["x","y"].map(k => `<label class="fld"><span>${k.toUpperCase()} (m)</span><input data-f="g.${k}" type="text" inputmode="decimal" value="${esc(g[k])}"></label>`).join("")}</div><div class="two">${[["w", t("f_w")], ["h", t("f_hgt")]].map(([k, l]) => `<label class="fld"><span>${esc(l)} (m)</span><input data-f="g.${k}" type="text" inputmode="decimal" value="${esc(g[k])}"></label>`).join("")}</div>` : `<button class="btn small" data-dr="bDrawRoom">▭ ${esc(t("bd_putOnPlan"))}</button>`}
      ${sec("breq", "📋 " + t("bd_needs"), `<table class="t">${RK.map(k => { const q = reqOf(r, k), pl = placedIn(b, r, k); return `<tr><td>${esc(kindName(k))}</td><td style="width:70px"><input data-f="q.${k}" type="text" inputmode="numeric" value="${q || ""}" style="width:56px"></td><td class="c ${q && pl < q ? "bad" : q ? "ok" : ""}">${pl}/${q}</td></tr>`; }).join("")}</table>
        <button class="btn small" data-dr="bCreate">＋ ${esc(t("bd_createMissing"))}</button>`, true)}
      ${sec("bdevs", "🔌 " + t("devices") + ` <span class="cnt">${b.devices.filter(d => d.room === r.id).length}</span>`, b.devices.filter(d => d.room === r.id).map(d => `<div class="lnk" data-dr="sel:${d.id}"><svg viewBox="0 0 48 48" width="18" height="18">${ICO[devIcon(d)] || ICO.box}</svg><span><b>${esc(devLabel(d))}</b> <small class="muted">${esc(kindName(d.kind))}${posOf(d) ? "" : " · " + t("bd_notOnPlan")}</small></span></div>`).join("") || `<p class="muted small">—</p>`)}
      <div class="btns"><button class="btn" data-dr="bDupRoom">⧉ ${esc(t("duplicate"))}</button><button class="btn dan" data-dr="bDelRoom">🗑 ${esc(t("delete"))}</button></div>`; }
  if (s.type === "bitem"){ const f = curFloor(b), it = f && fixFloorPlan(f).items.find(x => x.id === s.id); if (!it) return "";
    if (it.type === "boundary") return `${head(t(it.style === "house" ? "dw_house" : "dw_bound"), f.name)}
      <label class="fld"><span>${esc(t("f_text"))}</span><input data-f="i.text" value="${esc(it.text || "")}"></label>
      <label class="fld"><span>${esc(t("dw_bStyle"))}</span><select data-f="i.style">${opt("yard", t("dw_bound"), it.style || "yard")}${opt("house", t("dw_house"), it.style || "yard")}</select></label>
      <p class="muted small">${esc(t("dw_bInfo", {n:(it.pts || []).length / 2, w:r1(it.w), h:r1(it.h)}))}</p><p class="muted small">${esc(t("dw_bHint"))}</p>
      <div class="btns"><button class="btn" data-dr="bDupItem">⧉ ${esc(t("duplicate"))}</button><button class="btn dan" data-dr="bDelItem">🗑 ${esc(t("delete"))}</button></div>`;
    return `${head(itemName(it.type), f.name)}
      ${it.type === "yard" || DRAW.isSym(it.type) ? `<label class="fld"><span>${esc(t("f_text"))}</span><input data-f="i.text" value="${esc(it.text || (it.type === "yard" ? t("bi_yard") : ""))}"></label>` : ""}
      ${it.type === "sgate" ? `<label class="fld"><span>${esc(t("sg_side"))}</span><select data-f="i.side">${opt("l", "⬅ " + t("sg_left"), it.side || "l")}${opt("r", t("sg_right") + " ➡", it.side || "l")}</select></label><p class="muted small">${esc(t("sg_sideH"))}</p>` : ""}
      ${it.type === "label" ? `<label class="fld"><span>${esc(t("f_text"))}</span><input data-f="i.text" value="${esc(it.text || "")}"></label><label class="fld"><span>${esc(t("bd_fsize"))}</span><input data-f="i.size" type="text" inputmode="numeric" value="${esc(it.size || 12)}"></label>` : ""}
      <div class="two">${["x","y","w","h"].map(k => `<label class="fld"><span>${k === "w" ? esc(t("f_w")) : k === "h" ? esc(t("f_hgt")) : k.toUpperCase()} (m)</span><input data-f="i.${k}" type="text" inputmode="decimal" value="${esc(it[k])}"></label>`).join("")}</div>
      ${rotFld("i.rot", it.rot)}
      <div class="btns"><button class="btn" data-dr="bDupItem">⧉ ${esc(t("duplicate"))}</button><button class="btn dan" data-dr="bDelItem">🗑 ${esc(t("delete"))}</button></div>`; }
  if (s.type === "bwall"){ const f = curFloor(b), w = f && (f.plan.walls || []).find(x => x.id === s.id); if (!w) return "";
    const L = DRAW.wallLen(w), A = Math.round(Math.atan2(w.y2 - w.y1, w.x2 - w.x1) * 180 / Math.PI * 10) / 10, mats = ["drywall","brick","block","concrete","rcon","glass","wood","door","metal"];
    return `${head(t("dw_wall"), f.name)}
      <div class="two"><label class="fld"><span>${esc(t("dw_len"))} (m)</span><input data-f="w.len" type="text" inputmode="decimal" value="${esc(r2(L))}"></label>${rotFld("w.ang", A, t("dw_ang"))}</div>
      <div class="two"><label class="fld"><span>${esc(t("dw_thick"))} (cm)</span><input data-f="w.t" type="text" inputmode="decimal" value="${esc(Math.round(DRAW.wallT(w) * 100))}"></label><label class="fld"><span>${esc(t("dw_bend"))} (°)</span><input data-f="w.bend" type="text" inputmode="decimal" value="${esc(num(w.bend, 0))}"></label></div>
      <label class="fld"><span>${esc(t("dw_mat"))}</span><select data-f="w.mat">${mats.map(m => opt(m, t("wf_mat_" + m), w.mat || "drywall")).join("")}</select></label>
      ${w.kind === "door" ? `<label class="chk" title="${esc(t("dw_openH"))}"><input type="checkbox" data-f="w.open"${w.open ? " checked" : ""}> 🚪 ${esc(t("dw_open"))}</label>` : `<label class="chk" title="${esc(t("dw_lowH"))}"><input type="checkbox" data-f="w.low"${w.low ? " checked" : ""}> ${esc(t("dw_low"))}</label>`}
      <div class="two">${["x1","y1"].map(k => `<label class="fld"><span>${k.toUpperCase()} (m)</span><input data-f="w.${k}" type="text" inputmode="decimal" value="${esc(r2(w[k]))}"></label>`).join("")}</div>
      <p class="muted small">${esc(t("dw_wallInfo", {a:r1(DRAW.wallArc(w))}))}</p><p class="muted small">${esc(t("dw_wallHint2"))}</p>
      <div class="btns"><button class="btn" data-dr="bDupWall">⧉ ${esc(t("duplicate"))}</button><button class="btn" data-dr="bWallNext">↪ ${esc(t("dw_next"))}</button><button class="btn dan" data-dr="bDelWall">🗑 ${esc(t("delete"))}</button></div>`; }
  if (s.type === "bshape"){ const f = curFloor(b), o = f && (f.plan.shapes || []).find(x => x.id === s.id); if (!o) return "";
    return `${head(t("dw_pc_" + o.k) === "dw_pc_" + o.k ? o.k : t("dw_pc_" + o.k), f.name + (o.room && roomById(b, o.room) ? " · " + roomById(b, o.room).name : ""))}
      <div class="two">${["x","y","w","h"].map(k => `<label class="fld"><span>${k === "w" ? esc(t("f_w")) : k === "h" ? esc(t("f_hgt")) : k.toUpperCase()} (m)</span><input data-f="o.${k}" type="text" inputmode="decimal" value="${esc(r2(o[k]))}"></label>`).join("")}</div>
      ${rotFld("o.rot", o.rot)}
      ${o.k === "rwall" ? `<label class="fld"><span>${esc(t("dw_pcRoom"))}</span><select data-f="o.room">${opt("", t("none"), o.room || "")}${roomsOf(b, f).map(r => opt(r.id, r.name, o.room || "")).join("")}</select></label><p class="muted small">${esc(t("dw_pcRoomH"))}</p>` : ""}
      <label class="chk" title="${esc(t("dw_blockH"))}"><input type="checkbox" data-f="o.block"${(o.block !== undefined ? o.block : (o.p || []).some(([k]) => SH_BLOCK.test(k))) ? " checked" : ""}> 🧱 ${esc(t("dw_block"))}</label>
      ${(o.p || []).some(([k]) => k === "door") ? `<label class="chk" title="${esc(t("dw_openH"))}"><input type="checkbox" data-f="o.open"${o.open ? " checked" : ""}> 🚪 ${esc(t("dw_openSh"))}</label>` : ""}
      <p class="muted small">${esc(t("dw_pcHint"))}</p>
      <div class="btns">${o.w !== o.w0 || o.h !== o.h0 ? `<button class="btn" data-dr="bShReset">↺ ${esc(t("dw_pcReset"))}</button>` : ""}<button class="btn" data-dr="bSplit" title="${esc(t("dw_splitH"))}">✂ ${esc(t("dw_split"))}</button><button class="btn" data-dr="bDupShape">⧉ ${esc(t("duplicate"))}</button><button class="btn dan" data-dr="bDelShape">🗑 ${esc(t("delete"))}</button></div>`; }
  if (s.type === "rack"){ const r = rackById(b, s.id); if (!r) return "";
    return `${head(r.name, t("k_rack") === "k_rack" ? "Rack" : t("k_rack"))}<label class="fld"><span>${esc(t("f_name"))}</span><input data-f="k.name" value="${esc(r.name)}"></label>
      <label class="fld"><span>${esc(t("f_room"))}</span><select data-f="k.room">${opt("", t("none"), r.room)}${roomsOf(b, curFloor(b) || {}).map(x => opt(x.id, x.name, r.room)).join("")}</select></label>
      <div class="btns"><button class="btn" data-dr="bOpenRack">🗄 ${esc(t("bd_openRack"))}</button><button class="btn" data-dr="bUnplace">⤴ ${esc(t("removeFromView"))}</button></div>`; }
  if (s.type === "bfloor"){ const f = planFloor(b, s.id); if (!f) return ""; const p = fixFloorPlan(f);
    return `${head(f.name, isSite(f) ? t("flOut") : t("f_floor"))}${isSite(f) ? `<p class="muted small">${esc(t("sitePlanH"))}</p>` : ""}<label class="fld"><span>${esc(t("f_name"))}</span><input data-f="f.name" value="${esc(f.name)}"></label>
      <div class="two"><label class="fld"><span>${esc(t("f_w"))} (m)</span><input data-f="f.wm" type="text" inputmode="decimal" value="${esc(p.wm)}"></label><label class="fld"><span>${esc(t("bd_depth"))} (m)</span><input data-f="f.hm" type="text" inputmode="decimal" value="${esc(p.hm)}"></label></div>
      <div class="two">${isSite(f) ? "<span></span>" : `<label class="fld"><span>${esc(t("bd_fh"))} (m)</span><input data-f="f.h" type="text" inputmode="decimal" value="${esc(f.h || 3.5)}"></label>`}<label class="fld"><span>${esc(t("bd_ext"))} (m)</span><input data-f="f.ext" type="text" inputmode="decimal" value="${esc(num(p.ext, 15))}"></label></div>
      <div class="btns"><button class="btn" data-dr="bImg">🖼 ${esc(t("wf_loadImg"))}</button>${p.img ? `<button class="btn dan" data-dr="bImgRm">${esc(t("wf_rmImg"))}</button>` : ""}</div>
      <p class="muted small">${esc(t("bd_imgHint"))}</p>`; }
  return "";
}
function onField(path, v){
  const b = B(), s = UI.sel; if (!s) return;
  const n = x => r2(Math.max(0, num(String(x).replace(",", "."), 0)));   // to the centimetre
  if (s.type === "room"){ const r = roomById(b, s.id); if (!r) return;
    edit(() => { const [g, k] = path.split(".");
      if (g === "r"){ if (k === "users") r.users = Math.round(n(v)); else if (k === "floor"){ r.floor = v; b.devices.forEach(d => { if (d.room === r.id) d.floor = v; }); } else r[k] = String(v).trim() || r[k]; }
      else if (g === "g"){ r.geo[k] = k === "w" || k === "h" ? Math.max(.5, n(v)) : n(v); delete r.geo.est; }
      else if (g === "q"){ r.req[k] = clamp(Math.round(n(v)), 0, 200); } }); return; }   // at most 200 of a kind per room (a typed 99999 made 99999 devices)
  if (s.type === "bitem"){ const f = curFloor(b), it = f && f.plan.items.find(x => x.id === s.id); if (!it) return;
    edit(() => { const k = path.split(".")[1]; if (k === "text") it.text = v; else if (k === "style") it.style = v; else if (k === "side") it.side = v === "r" ? "r" : "l"; else if (k === "rot") it.rot = ((num(String(v).replace(",", "."), 0) % 360) + 360) % 360; else it[k] = k === "w" || k === "h" ? Math.max(.1, n(v)) : k === "size" ? clamp(n(v), 8, 40) : n(v); }); return; }
  if (s.type === "bwall"){ const f = curFloor(b), w = f && (f.plan.walls || []).find(x => x.id === s.id); if (!w) return; const k = path.split(".")[1], x = num(String(v).replace(",", "."), NaN);
    edit(() => { if (k === "mat"){ w.mat = v; return; } if (k === "low" || k === "open"){ if (v === true || v === "true" || v === "on") w[k] = true; else delete w[k]; return; } if (!isFinite(x)) return;
      const L = DRAW.wallLen(w), A = Math.atan2(w.y2 - w.y1, w.x2 - w.x1);
      if (k === "len"){ const n = Math.max(.1, x); w.x2 = r2(w.x1 + Math.cos(A) * n); w.y2 = r2(w.y1 + Math.sin(A) * n); }
      else if (k === "ang"){ const a = x * Math.PI / 180; w.x2 = r2(w.x1 + Math.cos(a) * L); w.y2 = r2(w.y1 + Math.sin(a) * L); }
      else if (k === "t") w.t = clamp(x / 100, .02, 1.5);
      else if (k === "bend") w.bend = clamp(Math.round(x), -300, 300);
      else if (k === "x1" || k === "y1"){ const d = x - w[k], o = k === "x1" ? "x2" : "y2"; w[k] = r2(x); w[o] = r2(w[o] + d); } }); return; }
  if (s.type === "bshape"){ const f = curFloor(b), o = f && (f.plan.shapes || []).find(x => x.id === s.id); if (!o) return; const k = path.split(".")[1];
    if (k === "open") return edit(() => { if (v === true || v === "true" || v === "on") o.open = true; else delete o.open; });
    if (k === "block") return edit(() => { o.block = v === true || v === "true" || v === "on"; });
    edit(() => { if (k === "room"){ o.room = v; return; } const x = num(String(v).replace(",", "."), NaN); if (!isFinite(x)) return; if (k === "rot") o.rot = ((x % 360) + 360) % 360; else if (k === "w" || k === "h") o[k] = Math.max(.05, r2(x)); else o[k] = r2(x); }); return; }
  if (s.type === "rack"){ const r = rackById(b, s.id); if (!r) return; edit(() => { const k = path.split(".")[1]; if (k === "name") r.name = String(v).trim() || r.name; else r.room = v; }); return; }
  if (s.type === "bfloor"){ const f = planFloor(b, s.id); if (!f) return; edit(() => { const k = path.split(".")[1]; if (k === "name") f.name = String(v).trim() || f.name; else if (k === "h") f.h = Math.max(2, n(v)); else if (k === "ext") f.plan.ext = clamp(n(v), 0, 500); else f.plan[k] = clamp(n(v), 2, 2000); }); }
}
async function onDrawerAct(k){
  const b = B(), s = UI.sel; if (!s) return; const f = curFloor(b);
  if (k === "bUnplace"){ edit(() => { if (s.type === "dev"){ const d = devById(b, s.id); if (d) clearPos(d); } else if (s.type === "rack"){ const r = rackById(b, s.id); if (r) delete r.pos; } }); return; }
  if (k === "bOpenRack"){ UI.rackSel = s.id; switchApp("rack"); UI.sel = {type:"rack", id:s.id}; render(); return; }
  if (k === "bImg"){ const id = await pickImage(); if (id) edit(() => { planFloor(b, s.id).plan.img = id; }); return; }
  if (k === "bImgRm"){ edit(() => { planFloor(b, s.id).plan.img = null; }); return; }
  if (s.type === "room"){ const r = roomById(b, s.id); if (!r) return;
    if (k === "bCreate"){ edit(() => createMissing(b, r)); toast("✓ " + t("bd_created")); return; }
    if (k === "bDelRoom") return delRoom(b, r);
    if (k === "bDupRoom"){ edit(() => { const c = Object.assign(clone(r), {id:uid("r"), name:r.name + " (2)"}); if (c.geo){ c.geo.x = r1(c.geo.x + 1); c.geo.y = r1(c.geo.y + 1); } b.rooms.push(c); UI.sel = {type:"room", id:c.id}; }); return; }
    if (k === "bDrawRoom"){ const fl = planFloor(b, r.floor) || f; if (!fl) return; edit(() => { r.geo = freeRect(b, fl, 4, 4); st().floor = fl.id; UI.tabs.building = "plan"; }); return; } }
  if (s.type === "bwall" && f){ const W = f.plan.walls, w = W.find(x => x.id === s.id); if (!w) return;
    if (k === "bDelWall") return edit(() => { f.plan.walls = W.filter(x => x !== w); UI.sel = null; });
    if (k === "bDupWall") return edit(() => { const c = Object.assign(clone(w), {id:uid("w"), x1:r2(w.x1 + .5), y1:r2(w.y1 + .5), x2:r2(w.x2 + .5), y2:r2(w.y2 + .5)}); W.push(c); UI.sel = {type:"bwall", id:c.id}; });
    if (k === "bWallNext") return edit(() => { const A = Math.atan2(w.y2 - w.y1, w.x2 - w.x1) + Math.PI / 2, L = DRAW.wallLen(w); const c = Object.assign(clone(w), {id:uid("w"), x1:w.x2, y1:w.y2, x2:r2(w.x2 + Math.cos(A) * L), y2:r2(w.y2 + Math.sin(A) * L), bend:0}); W.push(c); UI.sel = {type:"bwall", id:c.id}; }); }
  if (s.type === "bshape" && f){ const o = (f.plan.shapes || []).find(x => x.id === s.id); if (!o) return;
    if (k === "bDelShape") return edit(() => { f.plan.shapes = f.plan.shapes.filter(x => x !== o); UI.sel = null; });
    if (k === "bDupShape") return edit(() => { const c = Object.assign(clone(o), {id:uid("s"), x:r2(o.x + .5), y:r2(o.y + .5), room:""}); f.plan.shapes.push(c); UI.sel = {type:"bshape", id:c.id}; });
    if (k === "bShReset") return edit(() => { o.w = o.w0; o.h = o.h0; });
    if (k === "bSplit"){ const L = DRAW.splitShape(o); if (!L) return toast(t("dw_splitNo")); edit(() => { const i = f.plan.shapes.indexOf(o); f.plan.shapes.splice(i, 1, ...L); UI.sel = null; }); toast("✂ " + t("dw_splitDone", {n:L.length})); return; } }
  if (s.type === "bitem" && f){ const it = f.plan.items.find(x => x.id === s.id); if (!it) return;
    if (k === "bDelItem") edit(() => { f.plan.items = f.plan.items.filter(x => x !== it); UI.sel = null; });
    if (k === "bDupItem") edit(() => { const c = Object.assign(clone(it), {id:uid("i"), x:r1(it.x + .5), y:r1(it.y + .5)}); f.plan.items.push(c); UI.sel = {type:"bitem", id:c.id}; }); }
}
async function delRoom(b, r){
  const n = b.devices.filter(d => d.room === r.id).length;
  const ch = n ? await uiChoice(t("bd_delRoomQ",{r:r.name, n}), [["keep", t("bd_delKeep")], ["all", t("bd_delAll"), "dan"]]) : (await uiConfirm(t("bd_delRoomC",{r:r.name}), t("delete"), true)) ? "keep" : null;
  if (!ch) return;
  edit(() => { if (ch === "all") removeDevices(b, b.devices.filter(d => d.room === r.id).map(d => d.id)); else b.devices.forEach(d => { if (d.room === r.id) d.room = ""; });
    b.racks.forEach(k => { if (k.room === r.id) k.room = ""; }); b.rooms = b.rooms.filter(x => x !== r); UI.sel = null; });
}
// Devices a room still needs: created inside the room (spread along its walls).
function createMissing(b, r){
  const L = []; RK.forEach(k => { for (let i = placedIn(b, r, k); i < reqOf(r, k); i++) L.push(k); });
  const g = r.geo, n = L.length; let i = 0;
  L.forEach(k => { const d = newDevice(k, {floor:r.floor, room:r.id}); d.name = autoName(b, k); b.devices.push(d);
    if (g){ const per = Math.max(1, Math.ceil(n / 2)), row = i < per ? 0 : 1, col = row ? i - per : i, cnt = row ? n - per : per;
      setPos(d, g.x + g.w * (col + 1) / (cnt + 1), row ? g.y + g.h - Math.min(.8, g.h * .2) : g.y + (k === "ap" || k === "camera" || k === "sensor" ? g.h / 2 : Math.min(1.8, g.h * .4))); }
    i++; });
  return L.length;
}
function freeRect(b, f, w, h){ const p = fixFloorPlan(f); for (let y = 0; y + h <= p.hm; y += .5) for (let x = 0; x + w <= p.wm; x += .5){ if (!geoRooms(b, f).some(r => x < r.geo.x + r.geo.w && x + w > r.geo.x && y < r.geo.y + r.geo.h && y + h > r.geo.y)) return {x, y, w, h}; } return {x:0, y:0, w, h}; }

/* ---------- placing and dragging on the plan ---------- */
function ptOf(e, svg, f){ const R = svg.getBoundingClientRect(), E = num(svg.dataset.e, 0), W = f.plan.wm + 2 * E, H = f.plan.hm + 2 * E;
  return {x:clamp((e.clientX - R.left) / R.width * W - E, -E, f.plan.wm + E), y:clamp((e.clientY - R.top) / R.height * H - E, -E, f.plan.hm + E)}; }
function doPlace(key, b, f, p){
  edit(() => {
    if (key.startsWith("room:")){ const type = isSite(f) && key === "room:office" ? "outdoor" : key.slice(5), w = type === "corridor" ? 8 : 4, h = type === "corridor" ? 2 : 4;
      const r = normRoom({id:uid("r"), name:type === "office" || type === "outdoor" ? t("roomN",{n:roomsOf(b, f).length + 1}) : t("rt_" + type), floor:f.id, users:0, wall:"drywall", type, req:Object.assign({}, RDEF[type]), geo:{x:snap(Math.min(p.x, f.plan.wm - w)), y:snap(Math.min(p.y, f.plan.hm - h)), w, h}});
      b.rooms.push(r); UI.sel = {type:"room", id:r.id}; }
    else if (key.startsWith("item:")){ const type = key.slice(5), D = itemDef(type); const it = {id:uid("i"), type, x:snap(p.x), y:snap(p.y), w:D.w, h:D.h, rot:0}; if (type === "label"){ it.text = t("bd_label"); it.size = 14; } fixFloorPlan(f).items.push(it); UI.sel = {type:"bitem", id:it.id}; }
    else if (key === "rack"){ const r = {id:uid("k"), name:nextRackName(b), u:42, floor:f.id}; normRack(r); const rm = roomAtPt(b, f, p.x, p.y); if (rm) r.room = rm.id; r.pos = {x:r1(p.x), y:r1(p.y)}; b.racks.push(r); UI.sel = {type:"rack", id:r.id}; }
    else if (key.startsWith("dev:")){ const k = key.slice(4), rm = roomAtPt(b, f, p.x, p.y), d = newDevice(k, {floor:f.id, room:rm ? rm.id : ""}); d.name = autoName(b, k); if (d.kind === "camera" && rm && (rm.type === "outdoor" || /həyət|heyet|bahçe|bahce|yard|garden|çöl|outdoor|outside|exterior|dış|parking|otopark|darvaza|gate|fasad|facade|cephe/i.test(rm.name))) d.camera.loc = "out"; if (d.kind === "camera" && isSite(f)) d.camera.loc = "out"; setPos(d, p.x, p.y); b.devices.push(d); UI.sel = {type:"dev", id:d.id}; }
    else if (key.startsWith("put:")){ const d = devById(b, key.slice(4)); if (d){ setPos(d, p.x, p.y); d.floor = f.id; if (d.kind === "camera" && d.camera && isSite(f)) d.camera.loc = "out"; const rm = roomAtPt(b, f, p.x, p.y); if (rm && !d.room) d.room = rm.id; UI.sel = {type:"dev", id:d.id}; } }
  });
}
async function renameAt(b, f, type, id){
  if (type === "room"){ const r = roomById(b, id), n = await uiPrompt(t("f_name"), r.name); if (n && n.trim()) edit(() => { r.name = n.trim(); }); }
  else if (type === "dev"){ const d = devById(b, id), n = await uiPrompt(t("f_name"), d.name); if (n && n.trim() && !await nameOk(b, n, d.id)) return; if (n && n.trim()) edit(() => { d.name = n.trim(); }); }
  else if (type === "rack"){ const r = rackById(b, id), n = await uiPrompt(t("f_name"), r.name); if (n && n.trim()) edit(() => { r.name = n.trim(); }); }
  else if (type === "bitem"){ const it = f.plan.items.find(x => x.id === id); if (it && (it.type === "label" || it.type === "yard")){ const n = await uiPrompt(t("f_text"), it.text || ""); if (n !== null) edit(() => { it.text = n; }); } }
}
// wall ends snap to the ends of other walls (30 cm), else to the grid; Shift keeps the wall at steps of 15°
function wallSnap(f, p, self, ang, from){ let best = null, bd = .3;
  (f.plan.walls || []).forEach(w => { if (w === self) return; [[w.x1, w.y1], [w.x2, w.y2]].forEach(([x, y]) => { const d = Math.hypot(p.x - x, p.y - y); if (d < bd){ bd = d; best = {x, y}; } }); });
  if (best) return best;
  if (ang && from){ const L = Math.hypot(p.x - from.x, p.y - from.y), a = Math.round(Math.atan2(p.y - from.y, p.x - from.x) / (Math.PI / 12)) * (Math.PI / 12), Ls = st().grid ? Math.round(L * 2) / 2 : r1(L); return {x:r2(from.x + Math.cos(a) * Ls), y:r2(from.y + Math.sin(a) * Ls)}; }
  return {x:snap(p.x), y:snap(p.y)}; }
// drawing tools: a wall (press, drag, release; the tool stays on for the next wall) and outlines (click the corners;
// click the first corner again, double-click or Enter to close; Esc stops)
function toolDown(tool, b, f, p, e){
  const P = fixFloorPlan(f); P.walls = Array.isArray(P.walls) ? P.walls : [];
  if (tool === "wall" || tool === "wallc"){ const q = wallSnap(f, p, null, false), w = {id:uid("w"), x1:q.x, y1:q.y, x2:q.x, y2:q.y, kind:"wall", mat:"brick", t:.2, bend:tool === "wallc" ? 90 : 0};
    // the drawer opens only when the wall is finished, so the plan does not shift under the pointer while drawing
    const sn = snapshot(); P.walls.push(w); drag = {mode:"draw", w, k:"2", snap:sn, moved:false, p0:p}; const el = $("svg.bplan"); if (el){ el.outerHTML = planSvg(b, f); zpAll(); } return; }
  if (tool === "bound" || tool === "house"){ const x = snap(p.x), y = snap(p.y);
    if (poly && poly.f === f.id){ const it = P.items.find(o => o.id === poly.id); if (!it){ poly = null; return; }
      const n = it.pts.length / 2, close = n >= 3 && Math.hypot(x - it.pts[0], y - it.pts[1]) < .45, dbl = Date.now() - poly.t < 400 && n >= 3 && Math.hypot(x - it.pts[it.pts.length - 2], y - it.pts[it.pts.length - 1]) < .3;
      if (close || dbl){ finishPoly(); return; }
      it.pts.push(x, y); DRAW.boundBox(it); poly.t = Date.now(); persist(); render(); return; }
    const it = {id:uid("i"), type:"boundary", style:tool === "house" ? "house" : "yard", pts:[x, y], x, y, w:0, h:0, rot:0, text:""};
    pushUndo(snapshot()); P.items.push(it); poly = {id:it.id, f:f.id, t:Date.now()}; UI.sel = {type:"bitem", id:it.id}; persist(); render(); toast(t("dw_polyHint")); }
}
function finishPoly(cancel){ if (!poly) return; const b = B(), f = planFloor(b, poly.f), it = f && f.plan.items.find(o => o.id === poly.id); poly = null; place = null;
  if (it && (cancel || it.pts.length < 6)){ f.plan.items = f.plan.items.filter(o => o !== it); UI.sel = null; } else if (it) DRAW.boundBox(it);
  persist(); render(); }
function wire(){
  const onPlan = onPlanTab;
  document.addEventListener("dragstart", e => { const el = e.target.closest && e.target.closest("[data-bplace]"); if (!el || !onPlan()) return; place = el.dataset.bplace; e.dataTransfer.setData("text/plain", place); e.dataTransfer.effectAllowed = "copy"; });
  document.addEventListener("dragover", e => { if (onPlan() && e.target.closest && e.target.closest("svg.bplan")) e.preventDefault(); });
  document.addEventListener("drop", e => { const svg = e.target.closest && e.target.closest("svg.bplan"); if (!svg || !onPlan()) return; e.preventDefault(); const b = B(), f = curFloor(b), key = e.dataTransfer.getData("text/plain") || place; place = null; if (key) doPlace(key, b, f, ptOf(e, svg, f)); });
  document.addEventListener("click", e => { if (!onPlanTab() && !(UI.app === "building")) return;
    const pl = e.target.closest("[data-bplace]"); if (pl){ place = place === pl.dataset.bplace ? null : pl.dataset.bplace; render(); return; }
    const pu = e.target.closest("[data-bput]"); if (pu){ const k = "put:" + pu.dataset.bput; place = place === k ? null : k; render(); return; }
    const fl = e.target.closest("[data-bfl]"); if (fl){ st().floor = fl.dataset.bfl; UI.sel = {type:"bfloor", id:fl.dataset.bfl}; render(); return; }
    const a = e.target.closest("[data-ba]"); if (a){ act(a.dataset.ba); return; }
    const rs = e.target.closest("[data-brotset]"); if (rs){ const [pth, v] = rs.dataset.brotset.split(":"); onField(pth, v); return; } });
  document.addEventListener("toggle", e => { const d = e.target; if (d && d.dataset && d.dataset.bpdet){ const S = st(); S.pdet = S.pdet || {}; S.pdet[d.dataset.bpdet] = d.open; } }, true);
  document.addEventListener("change", e => { if (UI.app !== "building" && !onPlanTab()) return; const el = e.target, b = B();
    if (el.dataset.bopt){ st()[el.dataset.bopt] = el.checked; render(); return; }
    if (el.dataset.bvec){ const f = curFloor(b); if (f) edit(() => { f.plan.vec = el.checked; if (el.checked && f.plan.bgop === undefined) f.plan.bgop = (f.plan.shapes || []).length ? 0 : 35; }); return; }
    if (el.dataset.bmoverf){ store.settings.moveRf = el.checked; persist(); return; }
    if (el.dataset.bbgop){ const f = curFloor(b); if (f) edit(() => { f.plan.bgop = clamp(num(el.value, 0), 0, 100); }); return; }
    if (el.dataset.bfn){ const f = planFloor(b, el.dataset.bfn); if (f && el.value.trim()) edit(() => { f.name = el.value.trim(); }); return; }
    if (el.dataset.brn){ const r = roomById(b, el.dataset.brn); if (r && el.value.trim()) edit(() => { r.name = el.value.trim(); }); return; }
    if (el.dataset.brt){ const r = roomById(b, el.dataset.brt); if (r) edit(() => { r.type = el.value; }); return; }
    if (el.dataset.bru){ const r = roomById(b, el.dataset.bru); if (r) edit(() => { r.users = Math.max(0, Math.round(num(el.value, 0))); }); return; }
    if (el.dataset.brq){ const [id, k] = el.dataset.brq.split(":"), r = roomById(b, id); if (r) edit(() => { normRoom(r).req[k] = clamp(Math.round(num(el.value, 0)), 0, 200); }); } });
  document.addEventListener("pointerdown", e => {
    if (!onPlan() || (e.button !== 0 && e.pointerType !== "touch")) return; const svg = e.target.closest("svg.bplan"); if (!svg) return;
    const b = B(), f = curFloor(b); if (!f) return; const p = ptOf(e, svg, f);
    if (place && place.startsWith("tool:")){ e.preventDefault(); return toolDown(place.slice(5), b, f, p, e); }
    if (place){ e.preventDefault(); const k = place; place = null; doPlace(k, b, f, p); return; }
    const ro = e.target.closest("[data-brot]");
    if (ro){ const [ty, id] = ro.dataset.brot.split(":"), o = ty === "bshape" ? f.plan.shapes.find(x => x.id === id) : f.plan.items.find(x => x.id === id); if (o){ drag = {mode:"rot2", o, cx:o.x + o.w / 2, cy:o.y + o.h / 2, snap:snapshot(), moved:false, p0:p}; e.preventDefault(); } return; }
    const wh = e.target.closest("[data-bwh]");
    if (wh){ const [id, k] = wh.dataset.bwh.split(":"), w = f.plan.walls.find(x => x.id === id); if (w){ drag = {mode:"wend", w, k, snap:snapshot(), moved:false, p0:p}; e.preventDefault(); } return; }
    const wb = e.target.closest("[data-bwb]");
    if (wb){ const w = f.plan.walls.find(x => x.id === wb.dataset.bwb); if (w){ drag = {mode:"wbend", w, snap:snapshot(), moved:false, p0:p}; e.preventDefault(); } return; }
    const vx = e.target.closest("[data-bvx]");
    if (vx){ const [id, i] = vx.dataset.bvx.split(":"), it = f.plan.items.find(x => x.id === id); if (!it) return; e.preventDefault();
      if (e.altKey){ if (it.pts.length > 6) edit(() => { it.pts.splice(+i * 2, 2); DRAW.boundBox(it); }); return; }
      drag = {mode:"vx", it, i:+i, snap:snapshot(), moved:false, p0:p}; return; }
    const cr = e.target.closest("[data-camrot]");
    if (cr){ const d = devById(b, cr.dataset.camrot); drag = {mode:"rot", d, snap:snapshot(), moved:false, p0:p}; e.preventDefault(); return; }
    const lb = e.target.closest("[data-rlab]");
    if (lb && !(host() && host().lockRooms && false)){ const r = roomById(b, lb.dataset.rlab), g = r.geo, sx = g.pw ? g.w / g.pw : 1, sy = g.ph ? g.h / g.ph : 1;
      if (g.lx === undefined){ g.lx = .4 + 1.5 / sx; g.ly = .6 / sy; }
      UI.sel = {type:"room", id:r.id}; drag = {mode:"lab", g, sx, sy, lx:g.lx, ly:g.ly, p0:p, snap:snapshot(), moved:false}; e.preventDefault(); render(); return; }
    const res = e.target.closest("[data-res]"), dv = e.target.closest("[data-bdev]"), rk = e.target.closest("[data-brack]"), it = e.target.closest("[data-bitem]") || e.target.closest("[data-bbound]"), rm = e.target.closest("[data-room]"), wl = e.target.closest("[data-bwall]"), sh = e.target.closest("[data-bshape]");
    let type = null, id = null;
    if (res){ const [ty, i] = res.dataset.res.split(":"), o = ty === "room" ? roomById(b, i).geo : ty === "bshape" ? f.plan.shapes.find(x => x.id === i) : f.plan.items.find(x => x.id === i);
      // a room name keeps its place on the plan while the room outline is resized
      const lab = ty === "room" && o.lx !== undefined ? {x:o.lx * (o.pw ? o.w / o.pw : 1), y:o.ly * (o.ph ? o.h / o.ph : 1)} : null;
      drag = {mode:"resize", o, lab, p0:p, w0:o.w, h0:o.h, snap:snapshot(), moved:false}; e.preventDefault(); return; }
    if (dv){ type = "dev"; id = dv.dataset.bdev; } else if (rk){ type = "rack"; id = rk.dataset.brack; } else if (it){ type = "bitem"; id = it.dataset.bitem || it.dataset.bbound; } else if (wl){ type = "bwall"; id = wl.dataset.bwall; } else if (sh){ type = "bshape"; id = sh.dataset.bshape; } else if (rm){ type = "room"; id = rm.dataset.room; }
    if (!type){ if (UI.sel || UI.multi.size){ UI.sel = null; UI.multi.clear(); render(); } return; }
    const now = Date.now(); if (lastDown && lastDown.id === id && now - lastDown.t < 450){ lastDown = null; drag = null; e.preventDefault();
      const bo = type === "bitem" && f.plan.items.find(x => x.id === id); if (bo && bo.type === "boundary"){ edit(() => DRAW.boundInsert(bo, p.x, p.y)); return; }
      renameAt(b, f, type, id); return; } lastDown = {id, t:now};
    if (type === "dev" && (e.ctrlKey || e.metaKey || e.shiftKey)){ if (!UI.multi.size && UI.sel && UI.sel.type === "dev") UI.multi.add("dev:" + UI.sel.id); const k = "dev:" + id; UI.multi.has(k) ? UI.multi.delete(k) : UI.multi.add(k); UI.sel = null; render(); return; }
    UI.multi.clear(); UI.sel = {type, id}; e.preventDefault();
    const items = [];
    if (type === "dev"){ const d = devById(b, id); items.push({d, ...posOf(d)}); }
    else if (type === "rack"){ const r = rackById(b, id); items.push({o:r.pos, x:r.pos.x, y:r.pos.y}); }
    else if (type === "bitem"){ const o = f.plan.items.find(x => x.id === id); if (o.type === "boundary") items.push({pts:o.pts, p0:o.pts.slice(), o}); else items.push({o, x:o.x, y:o.y}); }
    else if (type === "bwall"){ const w = f.plan.walls.find(x => x.id === id); items.push({w, a:[w.x1, w.y1, w.x2, w.y2]}); }
    else if (type === "bshape"){ const o = f.plan.shapes.find(x => x.id === id); items.push({o, x:o.x, y:o.y}); }
    else if (host() && host().lockRooms){ render(); return; }
    else { const r = roomById(b, id); items.push({o:r.geo, x:r.geo.x, y:r.geo.y});
      // a room carries what lies inside it
      b.devices.filter(d => d.room === r.id && posOf(d)).forEach(d => items.push({d, ...posOf(d)}));
      b.racks.filter(k => k.room === r.id && k.pos).forEach(k => items.push({o:k.pos, x:k.pos.x, y:k.pos.y}));
      // … and its walls, doors and windows read from the drawing
      const mine = (f.plan.shapes || []).filter(o => o.room === r.id); mine.forEach(o => items.push({o, x:o.x, y:o.y}));
      // … and (setting) the hidden Wi-Fi walls of the drawing that lie on this room's outline
      if (mine.length && store.settings.moveRf !== false){ const g = r.geo, m = .35, inR = (x, y) => x >= g.x - m && x <= g.x + g.w + m && y >= g.y - m && y <= g.y + g.h + m;
        (f.plan.walls || []).filter(w => w.src === "dxf" && inR(w.x1, w.y1) && inR(w.x2, w.y2)).forEach(w => items.push({w, a:[w.x1, w.y1, w.x2, w.y2]})); } }
    drag = {mode:"move", type, id, items, p0:p, snap:snapshot(), moved:false};
    render();
  });
  document.addEventListener("pointermove", e => { if (!drag) return; const svg = $("svg.bplan"); if (!svg) return; const b = B(), f = curFloor(b), p = ptOf(e, svg, f), dx = p.x - drag.p0.x, dy = p.y - drag.p0.y;
    if (!drag.moved && Math.hypot(dx, dy) * scaleFor(f) < 3) return; drag.moved = true;
    if (drag.mode === "rot"){ const q = posOf(drag.d); if (q) drag.d.camera.dir = Math.round(Math.atan2(p.y - q.y, p.x - q.x) * 180 / Math.PI + 360) % 360; }
    else if (drag.mode === "rot2"){ let a = Math.atan2(p.y - drag.cy, p.x - drag.cx) * 180 / Math.PI + 90; a = e.shiftKey ? Math.round(a / 15) * 15 : Math.round(a); drag.o.rot = ((a % 360) + 360) % 360; }
    else if (drag.mode === "wend" || drag.mode === "draw"){ const w = drag.w, k = drag.k || "2", o = k === "1" ? "2" : "1", q = wallSnap(f, p, w, e.shiftKey, {x:w["x" + o], y:w["y" + o]}); w["x" + k] = q.x; w["y" + k] = q.y; }
    else if (drag.mode === "wbend"){ const w = drag.w, L = DRAW.wallLen(w); if (L > .05){ const mx = (w.x1 + w.x2) / 2, my = (w.y1 + w.y2) / 2, nx = (w.y2 - w.y1) / L, ny = -(w.x2 - w.x1) / L, hh = (p.x - mx) * nx + (p.y - my) * ny, a = 4 * Math.atan(2 * hh / L) * 180 / Math.PI; w.bend = Math.abs(a) < 3 ? 0 : clamp(Math.round(e.shiftKey ? Math.round(a / 15) * 15 : a), -300, 300); } }
    else if (drag.mode === "vx"){ drag.it.pts[drag.i * 2] = snap(p.x); drag.it.pts[drag.i * 2 + 1] = snap(p.y); DRAW.boundBox(drag.it); }
    else if (drag.mode === "lab"){ drag.g.lx = r1(drag.lx + dx / drag.sx); drag.g.ly = r1(drag.ly + dy / drag.sy); }
    else if (drag.mode === "resize"){ const o = drag.o; o.w = Math.max(.3, snap(drag.w0 + dx)); o.h = Math.max(.2, snap(drag.h0 + dy)); delete o.est; if (drag.lab){ o.lx = r1(drag.lab.x / (o.pw ? o.w / o.pw : 1)); o.ly = r1(drag.lab.y / (o.ph ? o.h / o.ph : 1)); } }
    else drag.items.forEach((it, i) => { const nx = (drag.type === "room" || drag.type === "bitem") && i === 0 ? snap(it.x + dx) : r1(it.x + dx), ny = (drag.type === "room" || drag.type === "bitem") && i === 0 ? snap(it.y + dy) : r1(it.y + dy);
      if (it.pts){ for (let k = 0; k < it.pts.length; k += 2){ it.pts[k] = r2(it.p0[k] + snap(dx)); it.pts[k + 1] = r2(it.p0[k + 1] + snap(dy)); } DRAW.boundBox(it.o); }
      else if (it.w){ it.w.x1 = r2(it.a[0] + snap(dx)); it.w.y1 = r2(it.a[1] + snap(dy)); it.w.x2 = r2(it.a[2] + snap(dx)); it.w.y2 = r2(it.a[3] + snap(dy)); }
      else if (it.d) setPos(it.d, nx, ny); else { it.o.x = nx; it.o.y = ny; } });
    // a drawing piece or a label alone: move its own group (a big site plan takes ~0.1 s to redraw); the full redraw follows on release
    const one = drag.items.length === 1 && drag.items[0].o && !drag.items[0].pts && (drag.type === "bshape" || drag.type === "bitem") && UI.sel ? svg.querySelector(`[data-${drag.type}="${UI.sel.id}"]`) : null;
    if (one){ const o = drag.items[0].o, s = scaleFor(f), W = o.w * s, H = o.h * s; one.setAttribute("transform", `translate(${(o.x * s).toFixed(1)} ${(o.y * s).toFixed(1)})${o.rot ? ` rotate(${o.rot} ${(W / 2).toFixed(1)} ${(H / 2).toFixed(1)})` : ""}`); return; }
    if (!redrawQ){ redrawQ = requestAnimationFrame(() => { redrawQ = 0; const svgEl = $("svg.bplan"); if (svgEl && drag){ svgEl.outerHTML = planSvg(B(), curFloor(B())); zpAll(); } }); } });
  let redrawQ = 0;
  const up = cancel => { if (!drag) return; const g = drag; drag = null; if (cancel){ render(); return; }
    // a wall drawn by a click without dragging (or too short) is not kept
    if (g.mode === "draw" && DRAW.wallLen(g.w) < .15){ const f = curFloor(B()); f.plan.walls = f.plan.walls.filter(x => x !== g.w); UI.sel = null; render(); return; }
    if (g.mode === "draw"){ UI.sel = {type:"bwall", id:g.w.id}; pushUndo(g.snap); persist(); render(); return; }
    if (g.moved){ const b = B(), f = curFloor(b);
      // a device or rack dropped in another room now belongs to that room
      if (g.mode === "move" && (g.type === "dev" || g.type === "rack")){ const o = g.type === "dev" ? devById(b, g.id) : rackById(b, g.id), P1 = g.type === "dev" ? posOf(o) : o.pos, rm = roomAtPt(b, f, P1.x, P1.y); if (rm) o.room = rm.id; }
      pushUndo(g.snap); normBuilding(b); persist(); }
    render(); };
  document.addEventListener("pointerup", () => up(false));
  document.addEventListener("pointercancel", () => up(true));
}
function onKey(e){
  if (poly && e.key === "Enter"){ e.preventDefault(); finishPoly(); return; }
  const b = B(), f = curFloor(b), s = UI.sel; if (!s || !f) return;
  if (e.key === "Delete" || e.key === "Backspace"){ e.preventDefault();
    if (s.type === "room") return delRoom(b, roomById(b, s.id));
    if (s.type === "bitem") return edit(() => { f.plan.items = f.plan.items.filter(x => x.id !== s.id); UI.sel = null; });
    if (s.type === "dev") return edit(() => { clearPos(devById(b, s.id)); UI.sel = null; });
    if (s.type === "rack") return edit(() => { delete rackById(b, s.id).pos; UI.sel = null; });
    if (s.type === "bwall") return edit(() => { f.plan.walls = f.plan.walls.filter(x => x.id !== s.id); UI.sel = null; });
    if (s.type === "bshape") return edit(() => { f.plan.shapes = f.plan.shapes.filter(x => x.id !== s.id); UI.sel = null; }); }
  if (e.key.startsWith("Arrow")){ e.preventDefault(); const k = e.ctrlKey || e.altKey || e.metaKey ? .01 : e.shiftKey ? .1 : .5, dx = e.key === "ArrowLeft" ? -k : e.key === "ArrowRight" ? k : 0, dy = e.key === "ArrowUp" ? -k : e.key === "ArrowDown" ? k : 0;
    edit(() => { if (s.type === "room"){ const g = roomById(b, s.id).geo; if (g){ g.x = r2(g.x + dx); g.y = r2(g.y + dy); } } else if (s.type === "bitem"){ const o = f.plan.items.find(x => x.id === s.id); o.x = r2(o.x + dx); o.y = r2(o.y + dy); if (Array.isArray(o.pts)) for (let i = 0; i + 1 < o.pts.length; i += 2){ o.pts[i] = r2(o.pts[i] + dx); o.pts[i + 1] = r2(o.pts[i + 1] + dy); } }
      else if (s.type === "dev"){ const d = devById(b, s.id), P1 = posOf(d); if (P1) setPos(d, P1.x + dx, P1.y + dy); }
      else if (s.type === "bwall"){ const w = f.plan.walls.find(x => x.id === s.id); if (w){ w.x1 = r2(w.x1 + dx); w.x2 = r2(w.x2 + dx); w.y1 = r2(w.y1 + dy); w.y2 = r2(w.y2 + dy); } }
      else if (s.type === "bshape"){ const o = f.plan.shapes.find(x => x.id === s.id); if (o){ o.x = r2(o.x + dx); o.y = r2(o.y + dy); } } else if (s.type === "rack"){ const r = rackById(b, s.id); if (r.pos){ r.pos.x = r1(r.pos.x + dx); r.pos.y = r1(r.pos.y + dy); } } }); }
}
async function act(k){
  const b = B();
  if (k === "wizard") return wizard();
  if (k === "dxf") return dxfImport();
  if (k === "lndDxf") return siteDxfImport();
  if (k === "alignFloors") return alignFloors();
  if (k.startsWith("lndMv:")){ const [dx, dy] = k.slice(6).split(",").map(Number), p = siteOf(b).plan;   // the whole landscape drawing together
    return edit(() => { (p.shapes || []).forEach(o => { if (o.k === "lnd"){ o.x = r2(o.x + dx); o.y = r2(o.y + dy); } }); (p.items || []).forEach(o => { if (o.src === "lnd"){ o.x = r2(o.x + dx); o.y = r2(o.y + dy); } }); }); }
  if (k === "lndDel"){ if (!await uiConfirm(t("lx_delQ"))) return; const p = siteOf(b).plan; return edit(() => { p.shapes = (p.shapes || []).filter(o => o.k !== "lnd"); p.items = (p.items || []).filter(o => o.src !== "lnd"); UI.sel = null; }); }
  if (k === "addFloor"){ const n = await uiPrompt(t("floorNew"), t("floorN",{n:b.floors.length + 1})); if (n === null) return;
    return edit(() => { const f = {id:uid("f"), name:n.trim() || t("floorN",{n:b.floors.length + 1}), lvl:b.floors.length}; b.floors.push(f); normBuilding(b); const p = b.floors[b.floors.length - 2]; if (p){ f.plan.wm = p.plan.wm; f.plan.hm = p.plan.hm; } st().floor = f.id; UI.sel = {type:"bfloor", id:f.id}; }); }
  if (k === "mergeDup"){ const f = curFloor(b), L = f ? dupRooms(b, f) : []; if (!L.length) return;
    if (!await uiConfirm(t("dw_dupQ",{l:L.map(([r, tw]) => `${r.name} → ${tw.name}`).join("\n")}))) return;
    return edit(() => L.forEach(([r, tw]) => { b.devices.forEach(d => { if (d.room === r.id) d.room = tw.id; }); b.racks.forEach(k2 => { if (k2.room === r.id) k2.room = tw.id; });
      RK.forEach(k2 => { if (num(r.req[k2]) > num(tw.req && tw.req[k2])){ tw.req = tw.req || {}; tw.req[k2] = num(r.req[k2]); } }); if (!num(tw.users) && num(r.users)) tw.users = r.users; b.rooms = b.rooms.filter(x => x !== r); })); }
  if (k === "createAll"){ let n = 0; edit(() => { b.rooms.forEach(r => { n += createMissing(b, normRoom(r)); }); }); toast("✓ " + t("bd_createdN",{n})); return; }
  if (k === "reqCsv"){ saveText(`${fileSafe(b.name)} - ${t("bd_reqT")}.csv`, csvText([t("f_floor"), t("f_room"), t("bd_type"), "m²", t("f_users"), ...RK.flatMap(x => [kindName(x) + " (" + t("bd_req") + ")", kindName(x) + " (" + t("bd_placed") + ")"])],
      b.rooms.map(r => [floorName(b, r.floor), r.name, t("rt_" + normRoom(r).type), area(r), num(r.users), ...RK.flatMap(x => [reqOf(r, x), placedIn(b, r, x)])])), "csv", "text/csv"); return; }
  const [a, id] = k.split(":"), f = id && planFloor(b, id);
  if (isSite(f) && (a === "fUp" || a === "fDown" || a === "delFloor")) return;
  if (a === "goFloor"){ st().floor = id; UI.tabs.building = "plan"; UI.sel = {type:"bfloor", id}; render(); return; }
  if (a === "selRoom"){ const r = roomById(b, id); st().floor = r.floor; UI.tabs.building = "plan"; UI.sel = {type:"room", id}; render(); return; }
  if (a === "fUp" || a === "fDown"){ const i = b.floors.indexOf(f), j = a === "fUp" ? i + 1 : i - 1; if (j < 0 || j >= b.floors.length) return; edit(() => { [b.floors[i], b.floors[j]] = [b.floors[j], b.floors[i]]; b.floors.forEach((x, n) => x.lvl = n); }); return; }
  if (a === "addRoom"){ edit(() => { const ty = isSite(f) ? "outdoor" : "office", r = normRoom({id:uid("r"), name:t("roomN",{n:roomsOf(b, f).length + 1}), floor:f.id, users:0, wall:"drywall", type:ty, req:Object.assign({}, RDEF[ty]), geo:freeRect(b, f, 4, 4)}); b.rooms.push(r); }); return; }
  if (a === "delRoom") return delRoom(b, roomById(b, id));
  if (a === "delFloor"){ const n = roomsOf(b, f).length, nd = b.devices.filter(d => d.floor === f.id).length;
    if (!await uiConfirm(t("bd_delFloorC",{f:f.name, r:n, d:nd}), t("delete"), true)) return;
    edit(() => { const rids = new Set(roomsOf(b, f).map(r => r.id)); b.rooms = b.rooms.filter(r => !rids.has(r.id)); b.devices.forEach(d => { if (d.floor === f.id || rids.has(d.room)){ d.floor = ""; if (rids.has(d.room)) d.room = ""; clearPos(d); } });
      b.racks.forEach(r => { if (r.floor === f.id){ r.floor = ""; r.room = ""; delete r.pos; } }); b.floors = b.floors.filter(x => x !== f); if (st().floor === f.id) st().floor = null; UI.sel = null; }); }
}

/* ---------- guided set-up: floors → rooms per floor → what each room needs ---------- */
function wizard(){
  const b = B(), W = {name:b.name, floors:3, under:0, area:400, h:3.5, F:[], step:0};
  const mkFloors = () => { const old = W.F; W.F = [];
    for (let i = -W.under; i < W.floors; i++){ const o = old.find(x => x.lv === i) || {lv:i, name:i < 0 ? t("bd_floorB",{n:-i}) : t("floorN",{n:i + 1}), rooms:i < 0 ? 2 : 6, server:i === 0, area:W.area, R:[]};
      if (W.prevArea !== undefined && o.area === W.prevArea) o.area = W.area; W.F.push(o); }
    W.prevArea = W.area; };
  const mkRooms = F => { const want = clamp(Math.round(num(F.rooms)), 0, 300) + (F.server ? 1 : 0), old = F.R; F.R = [];
    if (F.server) F.R.push(old.find(r => r.type === "server") || {name:t("rt_server"), type:"server", users:0, req:Object.assign({}, RDEF.server)});
    for (let i = 0; F.R.length < want; i++){ const o = old.filter(r => r.type !== "server")[i] || {name:t("roomN",{n:i + 1}), type:"office", users:2, req:Object.assign({}, RDEF.office)}; F.R.push(o); } };
  const steps = [
    () => `<h3>🧭 ${esc(t("bd_wz1"))}</h3><p class="muted small">${esc(t("bd_wz1h"))}</p>
      <label class="fld"><span>${esc(t("bldName"))}</span><input id="bw-name" value="${esc(W.name)}"></label>
      <div class="two"><label class="fld"><span>${esc(t("bd_wzFloors"))}</span><input id="bw-fl" type="text" inputmode="numeric" value="${W.floors}"></label><label class="fld"><span>${esc(t("bd_wzUnder"))}</span><input id="bw-un" type="text" inputmode="numeric" value="${W.under}"></label></div>
      <div class="two"><label class="fld"><span>${esc(t("bd_wzArea"))}</span><input id="bw-ar" type="text" inputmode="decimal" value="${W.area}"></label><label class="fld"><span>${esc(t("bd_fh"))} (m)</span><input id="bw-h" type="text" inputmode="decimal" value="${W.h}"></label></div>
      ${b.floors.length ? `<p class="lbox">${esc(t("bd_wzHas",{n:b.floors.length}))}</p>` : ""}
      <div class="lbox dxfbox"><b>📐 ${esc(t("dx_wzT"))}</b><p class="muted small">${esc(t("dx_wzH"))}</p><button class="btn pri small" data-m="dxf">📐 ${esc(t("dx_btn"))}</button></div>`,
    () => `<h3>🏬 ${esc(t("bd_wz2"))}</h3><p class="muted small">${esc(t("bd_wz2h"))}</p><div class="scroll" style="max-height:52vh"><table class="t"><tr><th>${esc(t("f_floor"))}</th><th>${esc(t("bd_wzRooms"))}</th><th>${esc(t("bd_wzArea"))}</th><th>${esc(t("rt_server"))}</th></tr>
      ${W.F.slice().reverse().map(F => `<tr><td><input data-wf="${F.lv}:name" value="${esc(F.name)}"></td><td><input data-wf="${F.lv}:rooms" type="text" inputmode="numeric" value="${F.rooms}" style="width:60px"></td><td><input data-wf="${F.lv}:area" type="text" inputmode="decimal" value="${F.area}" style="width:80px"></td><td class="c"><input type="checkbox" data-wf="${F.lv}:server"${F.server ? " checked" : ""}></td></tr>`).join("")}</table></div>`,
    () => `<h3>🚪 ${esc(t("bd_wz3"))}</h3><p class="muted small">${esc(t("bd_wz3h"))}</p><div class="scroll" style="max-height:56vh">${W.F.slice().reverse().map(F => `<details class="dsec" open><summary>🏬 ${esc(F.name)} <span class="cnt">${F.R.length}</span></summary><div class="dsb scroll"><table class="t wzt"><tr><th>${esc(t("f_room"))}</th><th>${esc(t("bd_type"))}</th><th>👤</th>${RK.slice(0, 8).map(k => `<th title="${esc(kindName(k))}">${RK_SHORT[k]}</th>`).join("")}</tr>
      ${F.R.map((r, i) => `<tr><td><input data-wr="${F.lv}:${i}:name" value="${esc(r.name)}" style="min-width:110px"></td><td><select data-wr="${F.lv}:${i}:type">${RTYPES.map(k => opt(k, t("rt_" + k), r.type)).join("")}</select></td><td><input data-wr="${F.lv}:${i}:users" type="text" inputmode="numeric" value="${r.users || ""}" style="width:38px"></td>${RK.slice(0, 8).map(k => `<td><input data-wr="${F.lv}:${i}:q.${k}" type="text" inputmode="numeric" value="${r.req[k] || ""}" style="width:38px"></td>`).join("")}</tr>`).join("")}</table></div></details>`).join("")}</div><p class="muted small">${RK.slice(0, 8).map(k => `${RK_SHORT[k]} = ${kindName(k)}`).join(" · ")}</p>`,
    () => { const nR = W.F.reduce((a, F) => a + F.R.length, 0), nD = W.F.reduce((a, F) => a + F.R.reduce((x, r) => x + RK.reduce((y, k) => y + num(r.req[k]), 0), 0), 0);
      return `<h3>✓ ${esc(t("bd_wz4"))}</h3><p>${esc(t("bd_wz4h",{f:W.F.length, r:nR, d:nD}))}</p>
      <label class="chk"><input type="checkbox" id="bw-layout" checked> ${esc(t("bd_wzLayout"))}</label>
      <label class="chk"><input type="checkbox" id="bw-devs" checked> ${esc(t("bd_wzDevs",{n:nD}))}</label>
      <label class="chk"><input type="checkbox" id="bw-racks" checked> ${esc(t("bd_wzRacks"))}</label>
      <p class="muted small">${esc(t("bd_wzAfter"))}</p>`; }
  ];
  const read = () => {
    const v = id => $(id) && $(id).value;
    if ($("#bw-fl")){ W.name = v("#bw-name").trim() || W.name; W.floors = clamp(Math.round(num(v("#bw-fl"), 1)), 1, 120); W.under = clamp(Math.round(num(v("#bw-un"), 0)), 0, 10); W.area = Math.max(10, num(String(v("#bw-ar")).replace(",", "."), 400)); W.h = Math.max(2, num(String(v("#bw-h")).replace(",", "."), 3.5)); mkFloors(); }
    $$("[data-wf]").forEach(el => { const [lv, k] = el.dataset.wf.split(":"), F = W.F.find(x => x.lv === +lv); if (!F) return; F[k] = el.type === "checkbox" ? el.checked : k === "name" ? el.value.trim() || F.name : num(String(el.value).replace(",", "."), F[k]); });
    $$("[data-wr]").forEach(el => { const [lv, i, k] = el.dataset.wr.split(":"), F = W.F.find(x => x.lv === +lv), r = F && F.R[+i]; if (!r) return;
      if (k.startsWith("q.")) r.req[k.slice(2)] = clamp(Math.round(num(el.value, 0)), 0, 200); else if (k === "users") r.users = Math.max(0, Math.round(num(el.value, 0)));
      else if (k === "type"){ if (r.type !== el.value){ r.type = el.value; r.req = Object.assign({}, RDEF[el.value]); } } else r[k] = el.value.trim() || r[k]; });
  };
  const draw = () => { modal(`<div class="wz">${steps[W.step]()}</div><div class="wzdots">${steps.map((_, i) => `<i class="${i === W.step ? "on" : ""}"></i>`).join("")}</div>
    <div class="mfoot"><button class="btn" data-m="close">${esc(t("cancel"))}</button><span class="grow"></span>${W.step ? `<button class="btn" data-m="back">‹ ${esc(t("back"))}</button>` : ""}<button class="btn pri" data-m="next">${esc(W.step === steps.length - 1 ? t("bd_wzBuild") : t("next") + " ›")}</button></div>`, {
      next: () => { read(); if (W.step === 1) W.F.forEach(mkRooms); if (W.step === steps.length - 1) return build(); W.step++; draw(); },
      back: () => { read(); W.step--; draw(); }, dxf: () => { closeModal(); dxfImport(); } }, {wide:true, nofocus:true});
    $$('[data-wr$=":type"]').forEach(el => el.addEventListener("change", () => { read(); draw(); })); };
  const build = () => {
    const layout = $("#bw-layout").checked, devs = $("#bw-devs").checked, racks = $("#bw-racks").checked; closeModal();
    edit(() => {
      b.name = W.name || b.name;
      const under = [], over = [];
      W.F.forEach(F => {
        const A = Math.max(10, num(F.area, W.area)), wm = r1(Math.sqrt(A * 2)), hm = r1(A / wm);
        const f = {id:uid("f"), name:F.name, lvl:0, h:W.h}; (F.lv < 0 ? under : over).push(f); f.plan = {wm, hm, img:null, op:60, cal:false, idf:null, walls:[], survey:[], items:[]};
        const R = F.R.map(x => normRoom({id:uid("r"), name:x.name, floor:f.id, users:num(x.users), wall:x.type === "server" ? "concrete" : "drywall", type:x.type, req:Object.assign({}, x.req)}));
        if (layout){ // rooms in two rows along a central corridor
          const cor = R.length > 2 ? 2 : 0, top = Math.ceil(R.length / 2), bot = R.length - top, rh = (hm - cor) / (bot ? 2 : 1);
          R.forEach((r, i) => { const row = i < top ? 0 : 1, n = row ? bot : top, j = row ? i - top : i, w = wm / n; r.geo = {x:r1(j * w), y:r1(row ? rh + cor : 0), w:r1(w), h:r1(rh)}; });
          if (cor) R.push(normRoom({id:uid("r"), name:t("rt_corridor"), floor:f.id, users:0, wall:"none", type:"corridor", req:Object.assign({}, RDEF.corridor), geo:{x:0, y:r1(rh), w:wm, h:cor}}));
        }
        b.rooms.push(...R);
        if (racks) R.filter(r => r.type === "server").forEach(r => { const k = {id:uid("k"), name:nextRackName(b), u:42, floor:f.id, room:r.id}; normRack(k); if (r.geo) k.pos = {x:r1(r.geo.x + r.geo.w / 2), y:r1(r.geo.y + r.geo.h / 2)}; b.racks.push(k); });
        f.__R = R;
      });
      b.floors = [...under, ...b.floors, ...over];
      b.floors.forEach((f, i) => f.lvl = i); normBuilding(b);
      if (devs) b.floors.forEach(f => (f.__R || []).forEach(r => createMissing(b, r)));
      b.floors.forEach(f => delete f.__R);
      b.struct = Object.assign(b.struct || {}, {wizard:true}); st().floor = over[0] ? over[0].id : under[0].id; UI.tabs.building = "plan"; UI.sel = null;
    });
    toast("✓ " + t("bd_built"));
  };
  mkFloors(); draw();
}

/* ---------- DXF drawing → floors, rooms, walls, doors, windows, outlets ---------- */
/* ---------- floors lined up over each other ---------- */
// every floor keeps its own drawing; plan.ox / plan.oy say where it stands in the building (metres, the reference floor at 0, 0).
// The ground floor (else the floor with most walls) is the reference; the others are lined up floor by floor going up and down
// from it, each on the one next to it (exterior walls, columns, shafts and stairs stand over each other).
function floorShifts(floors, linesOf){ const L = floors.map(linesOf), n = floors.length; if (n < 2) return null;
  let ref = floors.findIndex(f => /zemin|zəmin|ground|giriş|giris|первый/i.test(f.name)); if (ref < 0) ref = floors.findIndex(f => num(f.lv, NaN) === 0); if (ref < 0 || !L[ref].length) ref = L.reduce((m, x, i) => x.length > L[m].length ? i : m, 0);
  const out = floors.map(() => null); out[ref] = {dx:0, dy:0, f:1, ref:true};
  const go = (i, j) => { if (!out[j] || !L[i].length || !L[j].length){ return; } const r = DXF.floorShift(L[i], L[j]); if (r) out[i] = {dx:r.dx + out[j].dx, dy:r.dy + out[j].dy, f:r.f}; };
  for (let i = ref + 1; i < n; i++) go(i, out[i - 1] ? i - 1 : ref);
  for (let i = ref - 1; i >= 0; i--) go(i, out[i + 1] ? i + 1 : ref);
  return out; }
async function alignFloors(){
  const b = B(), F = b.floors.filter(f => f.plan); toast("⏳ " + t("fa_busy")); await new Promise(r => setTimeout(r, 60));
  const R = floorShifts(F, f => { const w = siteWalls(f.plan); return w ? w.S : []; }); if (!R) return;
  const ok = F.filter((f, i) => R[i] && !R[i].ref), bad = F.filter((f, i) => !R[i]);
  if (!ok.length) return uiAlert(t("fa_none"));
  if (!await uiConfirm(t("fa_q",{l:F.map((f, i) => R[i] ? `${f.name}: ${R[i].ref ? t("fa_ref") : `${R[i].dx >= 0 ? "+" : ""}${R[i].dx} m, ${R[i].dy >= 0 ? "+" : ""}${R[i].dy} m (${Math.round(R[i].f * 100)}%)`}` : `${f.name}: ${t("fa_no")}`).join("\n")}))) return;
  edit(() => { F.forEach((f, i) => { if (R[i]){ f.plan.ox = R[i].dx; f.plan.oy = R[i].dy; } }); st().ghost = true; });
  toast("✓ " + t("fa_done",{n:ok.length}) + (bad.length ? " · " + t("fa_skip",{l:bad.map(f => f.name).join(", ")}) : "")); }
/* ---------- a landscape project (DXF) on the site plan ---------- */
// building walls already on the site plan: their box and the distance from a point to the nearest one (1 m grid)
function siteWalls(p){ const S = [], W = /^(wall|wallExt)(:f)?$/; let bb = null; const grow = (x, y) => { if (!bb) bb = [x, y, x, y]; else { bb[0] = Math.min(bb[0], x); bb[1] = Math.min(bb[1], y); bb[2] = Math.max(bb[2], x); bb[3] = Math.max(bb[3], y); } };
  (p.shapes || []).forEach(sh => { if (!sh.p.some(([k]) => W.test(k))) return; const kx = sh.w / (sh.w0 || sh.w), ky = sh.h / (sh.h0 || sh.h), a = (sh.rot || 0) * Math.PI / 180, ca = Math.cos(a), sa = Math.sin(a), cx = sh.w / 2, cy = sh.h / 2;
    const T = (x, y) => { x *= kx; y *= ky; if (a){ const dx = x - cx, dy = y - cy; x = cx + dx * ca - dy * sa; y = cy + dx * sa + dy * ca; } return [sh.x + x, sh.y + y]; };
    sh.p.forEach(([k, d]) => { if (!W.test(k)) return; String(d).split(/(?=M)/).forEach(part => { const n = part.match(/-?\d*\.?\d+(?:e-?\d+)?/g) || []; let pr = null; for (let i = 0; i + 1 < n.length; i += 2){ const q = T(+n[i], +n[i + 1]); grow(q[0], q[1]); if (pr) S.push([pr[0], pr[1], q[0], q[1]]); pr = q; } }); }); });
  if (!S.length) (p.walls || []).forEach(w => { if (w.low) return; S.push([w.x1, w.y1, w.x2, w.y2]); grow(w.x1, w.y1); grow(w.x2, w.y2); });
  if (!S.length) return null;
  const G = new Map(); S.forEach((s, i) => { for (let gx = Math.floor(Math.min(s[0], s[2])); gx <= Math.floor(Math.max(s[0], s[2])); gx++) for (let gy = Math.floor(Math.min(s[1], s[3])); gy <= Math.floor(Math.max(s[1], s[3])); gy++){ const k = gx + "," + gy; (G.get(k) || G.set(k, []).get(k)).push(i); } });
  const near = (x, y) => { let d = Infinity; for (let gx = Math.floor(x) - 1; gx <= Math.floor(x) + 1; gx++) for (let gy = Math.floor(y) - 1; gy <= Math.floor(y) + 1; gy++) (G.get(gx + "," + gy) || []).forEach(i => { const [x1, y1, x2, y2] = S[i], ex = x2 - x1, ey = y2 - y1, L2 = ex * ex + ey * ey || 1e-9, u = clamp(((x - x1) * ex + (y - y1) * ey) / L2, 0, 1); d = Math.min(d, Math.hypot(x - x1 - ex * u, y - y1 - ey * u)); }); return d; };
  const pts = []; S.forEach(q => pts.push(q[0], q[1], q[2], q[3]));
  return {bb, near, pts, S}; }
async function siteDxfImport(){
  const b = B(), f = siteOf(b), p = f.plan;
  const file = await new Promise(res => { const i = document.createElement("input"); i.type = "file"; i.accept = ".dxf,.DXF"; i.onchange = () => res(i.files[0] || null); i.oncancel = () => res(null); i.click(); });
  if (!file) return;
  if (/\.dwg$/i.test(file.name)) return uiAlert(t("dx_dwg"));
  toast("⏳ " + t("dx_reading",{f:file.name})); await new Promise(r => setTimeout(r, 60));
  let doc, flat, A;
  try { doc = DXF.parse(DXF.decode(await file.arrayBuffer())); flat = DXF.flatten(doc); A = DXF.analyze(doc, flat); }
  catch(e){ console.error(e); return uiAlert(e.message === "binary" ? t("dx_binary") : t("dx_fail") + " " + e.message); }
  if (!flat.segs.length) return uiAlert(t("dx_empty"));
  const LR = ["wall","plant","light","water","road","edge","curb","pave","stair","furn","hard","other","ignore"];
  const S = {roles:{}, scale:A.scale, units:A.units, clip:true, replace:(p.shapes || []).some(o => o.k === "lnd") || (p.items || []).some(o => o.src === "lnd"), labels:true};
  A.layers.forEach(l => S.roles[l.name] = l.hidden ? "ignore" : DXF.lroleOf(l.name));
  // the floor whose pieces were copied onto the site plan (most identical pieces, one shift): the drawing is matched to that
  // floor's walls alone (other floors' walls only confuse it) and moved by the same shift; else to the walls on the site plan
  let base = null; const sig = o => [o.w0, o.h0, ((o.p || [])[0] || [])[1]].join("|").slice(0, 120);
  b.floors.forEach(fl => { const m = new Map(); (fl.plan && fl.plan.shapes || []).forEach(o => m.set(sig(o), o)); const V = new Map();
    (p.shapes || []).forEach(o => { const q = m.get(sig(o)); if (!q) return; const k = (o.x - q.x).toFixed(1) + "," + (o.y - q.y).toFixed(1); V.set(k, (V.get(k) || 0) + 1); });
    const top = [...V.entries()].sort((x, y) => y[1] - x[1])[0]; if (top && top[1] >= 3 && (!base || top[1] > base.n)){ const [dx, dy] = top[0].split(",").map(Number); base = {f:fl, n:top[1], dx, dy}; } });
  const target = base ? siteWalls(base.f.plan) : siteWalls(p);
  // building outlines in the drawing (house, garage …): kept as walls that block the cameras; the user can untick one (a pergola)
  const outl = () => { S.out = DXF.wallOutlines(flat, S.roles, S.scale).filter(o => { if (!S.fit) return true; const q = S.fit.M(o.cx, o.cy); return q[0] > -5 && q[1] > -5 && q[0] < num(p.wm, 40) + 5 && q[1] < num(p.hm, 40) + 5; }); S.keep = S.keep || {}; S.out.forEach(o => { if (S.keep[o.i] === undefined) S.keep[o.i] = true; }); };
  S.dropFloor = true;
  const copies = () => { const all = new Set(); b.floors.forEach(fl => (fl.plan && fl.plan.shapes || []).forEach(o => all.add(sig(o)))); return (p.shapes || []).filter(o => o.k !== "lnd" && all.has(sig(o))); };
  const outSvg = () => { if (!S.out.length) return ""; const bb = DXF.bbox(S.out.flatMap(o => DXF.bbox(o.s.p))), W = 520, k = W / Math.max(bb[2] - bb[0], bb[3] - bb[1]), H = Math.round((bb[3] - bb[1]) * k);
    return `<svg viewBox="-8 -8 ${W + 16} ${H + 16}" width="100%" style="max-width:${W + 16}px;background:#fff;border-radius:8px">${S.out.map((o, n) => { let d = ""; for (let q = 0; q + 1 < o.s.p.length; q += 2) d += (q ? "L" : "M") + ((o.s.p[q] - bb[0]) * k).toFixed(1) + " " + ((bb[3] - o.s.p[q + 1]) * k).toFixed(1);
      return `<path d="${d}Z" fill="${S.keep[o.i] ? "rgba(17,23,34,.12)" : "none"}" stroke="${S.keep[o.i] ? "#111722" : "#9aa1ad"}" stroke-width="${S.keep[o.i] ? 2.4 : 1.2}" stroke-dasharray="${S.keep[o.i] ? "" : "5 3"}"/><text x="${((o.cx - bb[0]) * k).toFixed(1)}" y="${((bb[3] - o.cy) * k + 5).toFixed(1)}" text-anchor="middle" font-size="14" font-weight="800" fill="#c2410c">${n + 1}</text>`; }).join("")}</svg>`; };
  const fit = () => { const r = DXF.siteFit(flat, S.scale, target); S.fit = r && base ? Object.assign(r, {M0:r.M, M:(X, Y) => { const q = r.M0(X, Y); return [q[0] + base.dx, q[1] + base.dy]; }, fl:base.f.name}) : r; };
  fit(); outl();
  const draw = () => {
    const L = A.layers.filter(l => l.segs + l.texts > 0), cnt = r => L.filter(l => S.roles[l.name] === r).length;
    modal(`<h3>🌳 ${esc(t("lx_title"))} <small class="muted">${esc(file.name)}</small></h3>
      <p class="muted small">${esc(t("lx_intro"))}</p>
      <div class="lbox">${S.fit ? `✅ ${esc(t("lx_fitOk",{l:S.fit.L, p:Math.round(S.fit.score * 100)}) + (S.fit.fl ? " (" + S.fit.fl + ")" : ""))}<br><small class="muted">${esc(t("lx_fitTune"))}</small>` : `⚠ ${esc(target ? t("lx_fitNo") : t("lx_fitNoWalls"))}`}</div>
      <div class="two"><label class="fld"><span>${esc(t("dx_units"))}</span><select id="lx-u">${Object.values(DXF.UNITS).map(([u, k]) => opt(u, u + " (1 = " + k + " m)", S.units)).join("")}</select></label><span></span></div>
      ${S.fit ? `<label class="chk"><input type="checkbox" id="lx-clip"${S.clip ? " checked" : ""}> ${esc(t("lx_clip"))}</label>` : ""}
      ${S.out.length ? `<div class="lbox"><b>🏠 ${esc(t("lx_outT"))}</b><p class="muted small">${esc(t("lx_outH"))}</p>${outSvg()}
        <div class="btns" style="gap:10px;flex-wrap:wrap">${S.out.map((o, n) => `<label class="chk"><input type="checkbox" data-lxo="${o.i}"${S.keep[o.i] ? " checked" : ""}> <b>${n + 1}</b> · ${esc(o.w + " × " + o.h + " m")}</label>`).join("")}</div>
        ${copies().length ? `<label class="chk"><input type="checkbox" id="lx-dropFloor"${S.dropFloor ? " checked" : ""}> ${esc(t("lx_dropFloor",{n:copies().length}))}</label>` : ""}</div>` : ""}
      <label class="chk"><input type="checkbox" id="lx-labels"${S.labels ? " checked" : ""}> ${esc(t("lx_labels"))}</label>
      ${(p.shapes || []).some(o => o.k === "lnd") || (p.items || []).some(o => o.src === "lnd") ? `<label class="chk"><input type="checkbox" id="lx-replace"${S.replace ? " checked" : ""}> ${esc(t("lx_replace"))}</label>` : ""}
      <details class="dsec" open><summary>🗂 ${esc(t("dx_layers"))} <span class="cnt">${L.length}</span> <small class="muted">${esc(["plant","light","pave","hard","ignore"].map(r => t("lxr_" + r) + " " + cnt(r)).join(" · "))}</small></summary>
        <div class="dsb scroll" style="max-height:38vh"><p class="muted small">${esc(t("lx_layersH"))}</p><table class="t">${L.map(l => `<tr><td>${esc(l.name)}${l.hidden ? ` <small class="muted">(${esc(t("dx_hid"))})</small>` : ""}</td><td class="c small">${l.segs || ""}</td><td class="c small">${l.texts ? "T" + l.texts : ""}</td><td><select data-lxr="${esc(l.name)}">${LR.map(r => opt(r, t("lxr_" + r), S.roles[l.name])).join("")}</select></td></tr>`).join("")}</table></div></details>
      <div class="mfoot"><button class="btn" data-m="close">${esc(t("cancel"))}</button><span class="grow"></span><button class="btn pri" data-m="go">✓ ${esc(t("lx_go"))}</button></div>`,
      {go:() => { read(); create(); }}, {wide:true, nofocus:true});
    $$("[data-lxr],#lx-u,[data-lxo]").forEach(el => el.addEventListener("change", () => { read(); if (el.id === "lx-u") fit(); if (el.id === "lx-u" || el.dataset.lxr) outl(); draw(); }));
  };
  const read = () => {
    $$("[data-lxr]").forEach(el => S.roles[el.dataset.lxr] = el.value);
    const u = $("#lx-u"); if (u){ const U = Object.values(DXF.UNITS).find(x => x[0] === u.value); if (U){ S.units = U[0]; S.scale = U[1]; } }
    ["clip","labels","replace","dropFloor"].forEach(k => { const c = $("#lx-" + k); if (c) S[k] = c.checked; });
    $$("[data-lxo]").forEach(el => { S.keep[el.dataset.lxo] = el.checked; });
  };
  const create = async () => {
    closeModal(); toast("⏳ " + t("dx_building")); await new Promise(r => setTimeout(r, 60));
    let M, box = null, grow = null;
    if (S.fit){ M = S.fit.M;
      // what lies on the plot (its boundary, else the site plan) and a little around it
      const bd = (p.items || []).filter(it => it.type === "boundary"); let bb = null; bd.forEach(it => { DRAW.boundBox(it); const q = [it.x, it.y, it.x + it.w, it.y + it.h]; bb = bb ? [Math.min(bb[0], q[0]), Math.min(bb[1], q[1]), Math.max(bb[2], q[2]), Math.max(bb[3], q[3])] : q; });
      box = bb ? [bb[0] - 3, bb[1] - 3, bb[2] + 3, bb[3] + 3] : [-1, -1, p.wm + 1, p.hm + 1]; }
    else { // no building to match: the whole drawing in the corner of the site plan, the plan made big enough
      const bb = DXF.bbox(flat.segs.filter(s => (S.roles[s.L] || "other") !== "ignore").flatMap(s => s.p)); if (!bb) return uiAlert(t("dx_empty"));
      M = (X, Y) => [1 + (X - bb[0]) * S.scale, 1 + (bb[3] - Y) * S.scale]; grow = [Math.ceil((bb[2] - bb[0]) * S.scale + 2), Math.ceil((bb[3] - bb[1]) * S.scale + 2)]; }
    const names = new Set(b.rooms.filter(r => r.floor === OUT_FLOOR).map(r => r.name.toLocaleUpperCase("tr")));
    const plots = (p.items || []).filter(it => it.type === "boundary" && (it.pts || []).length >= 6).map(it => it.pts);
    const inPlot = plots.length ? (x, y) => plots.some(P => { let c = false, d = Infinity; for (let i = 0, j = P.length - 2; i < P.length; j = i, i += 2){ const xi = P[i], yi = P[i + 1], xj = P[j], yj = P[j + 1];
      if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c; const ex = xi - xj, ey = yi - yj, L2 = ex * ex + ey * ey || 1e-9, u = clamp(((x - xj) * ex + (y - yj) * ey) / L2, 0, 1); d = Math.min(d, Math.hypot(x - xj - ex * u, y - yj - ey * u)); }
      return c || d < 1.5; }) : null;
    const solids = S.out.filter(o => S.keep[o.i]).map(o => o.s), drop = S.dropFloor && solids.length ? new Set(copies()) : null;
    const R = DXF.landscape(flat, {roles:S.roles, M, box, inPlot, solids, clip:S.fit && S.clip ? S.fit.poly : null, scale:S.scale, skipText:s => names.has(s.toLocaleUpperCase("tr"))});
    if (!R.shapes.length && !R.labels.length) return uiAlert(t("lx_none"));
    edit(() => {
      if (S.replace){ p.shapes = (p.shapes || []).filter(o => o.k !== "lnd"); p.items = (p.items || []).filter(o => o.src !== "lnd"); }
      // the floor's pieces copied onto the site plan give way to the building walls of the drawing
      if (drop) p.shapes = (p.shapes || []).filter(o => !drop.has(o));
      if (grow){ p.wm = Math.max(num(p.wm, 0), grow[0]); p.hm = Math.max(num(p.hm, 0), grow[1]); }
      // landscape under the building pieces
      p.shapes = R.shapes.map(o => Object.assign(o, {id:uid("s")})).concat(p.shapes || []); p.vec = true; if (p.bgop === undefined) p.bgop = 0;
      if (S.labels) R.labels.forEach(l => { const size = l.h > .3 ? 12 : 10, w = Math.round((l.text.length * size * .6 / scaleFor(f) + .2) * 100) / 100;
        p.items.push({id:uid("i"), type:"label", src:"lnd", x:Math.round((l.x - w / 2) * 100) / 100, y:Math.round((l.y - .4) * 100) / 100, w, h:.8, rot:l.rot || 0, text:l.text, size}); });
      p.lndDxf = file.name; UI.sel = null; });
    toast("✓ " + t("lx_done",{n:R.shapes.length, l:S.labels ? R.labels.length : 0}) + (S.fit ? "" : " — " + t("lx_corner")));
  };
  draw();
}
async function dxfImport(){
  const file = await new Promise(res => { const i = document.createElement("input"); i.type = "file"; i.accept = ".dxf,.DXF"; i.onchange = () => res(i.files[0] || null); i.oncancel = () => res(null); i.click(); });
  if (!file) return;
  if (/\.dwg$/i.test(file.name)) return uiAlert(t("dx_dwg"));
  toast("⏳ " + t("dx_reading",{f:file.name}));
  await new Promise(r => setTimeout(r, 60));
  let doc, flat, A;
  try { doc = DXF.parse(DXF.decode(await file.arrayBuffer())); flat = DXF.flatten(doc); A = DXF.analyze(doc, flat); }
  catch(e){ console.error(e); return uiAlert(e.message === "binary" ? t("dx_binary") : t("dx_fail") + " " + e.message); }
  if (!flat.segs.length) return uiAlert(t("dx_empty"));
  const S = {roles:{}, kinds:{}, scale:A.scale, units:A.units, devs:true, req:true, walls:true, furn:true, align:true, labels:true, F:[], mode:B().floors.length || B().devices.length ? "over" : "add"};
  A.layers.forEach(l => S.roles[l.name] = l.role); A.blocks.forEach(x => S.kinds[x.name] = x.kind);
  const ROLES = ["wallExt","wall","door","window","column","stair","area","roomName","site","furn","other","ignore"];
  const lvOf = n => { const x = String(n).toLocaleLowerCase("tr"); if (/bodrum|zirzəmi|zirzemi|basement|podval|подвал|цокол/.test(x)) return -1; if (/zemin|ground|giriş|giris|1-?ci mərtəbə|первый/.test(x)) return 0; if (/çatı|cati|roof|çardaq|cherdak/.test(x)) return 50; const m = x.match(/(\d+)/); return m ? +m[1] : null; };
  const scan = () => { const G = DXF.floors(flat, S.roles, S.scale), old = S.F; S.F = G.map((g, i) => { const r = DXF.build(flat, {bb:g.bb, roles:S.roles, scale:S.scale, kinds:{}, furn:false}); const nm = r.title || g.title || t("floorN",{n:i + 1}), o = old[i] || {};
      return {g, on:o.on !== undefined ? o.on : r.rooms.length > 0 || G.length === 1, name:o.name || nm, lv:o.lv !== undefined ? o.lv : (lvOf(nm) ?? i), rooms:r.rooms.length, doors:r.doors, windows:r.windows, wm:r.wm, hm:r.hm}; }); };
  scan();
  const roleSel = l => `<select data-dxr="${esc(l.name)}">${ROLES.map(r => opt(r, t("dxr_" + r), S.roles[l.name])).join("")}</select>`;
  const kindSel = x => `<select data-dxk="${esc(x.name)}">${opt("", t("none"), S.kinds[x.name])}${["outlet","ap","camera","tv","phone","access","intercom","sensor","iot","printer"].map(k => opt(k, kindName(k), S.kinds[x.name])).join("")}</select>`;
  const draw = () => {
    const cnt = r => A.layers.filter(l => S.roles[l.name] === r).length, nOut = A.blocks.filter(x => S.kinds[x.name]).reduce((a, x) => a + x.n, 0);
    modal(`<h3>📐 ${esc(t("dx_title"))} <small class="muted">${esc(file.name)}</small></h3>
      <p class="muted small">${esc(t("dx_found",{f:S.F.length, u:S.units}))}${flat.hidden.length ? " " + t("dx_hidden",{n:flat.hidden.length}) : ""}</p>
      <div class="dxprev">${DXF.preview(flat, S.roles, S.F.map(F => Object.assign({}, F.g, {title:F.name})), 760)}</div>
      <div class="scroll"><table class="t"><tr><th></th><th>#</th><th>${esc(t("f_floor"))}</th><th title="${esc(t("dx_lvH"))}">${esc(t("dx_lv"))}</th><th>${esc(t("dx_size"))}</th><th>${esc(t("rooms"))}</th><th>🚪</th><th>🪟</th></tr>
        ${S.F.map((F, i) => `<tr><td><input type="checkbox" data-dxf="${i}:on"${F.on ? " checked" : ""}></td><td>${i + 1}</td><td><input data-dxf="${i}:name" value="${esc(F.name)}" style="min-width:140px"></td><td><input data-dxf="${i}:lv" type="text" inputmode="numeric" value="${F.lv}" style="width:48px"></td><td class="nw">${esc(F.wm + " × " + F.hm + " m")}</td><td class="c">${F.rooms}</td><td class="c">${F.doors}</td><td class="c">${F.windows}</td></tr>`).join("")}</table></div>
      ${B().floors.length || B().devices.length ? `<div class="lbox"><b>${esc(t("ov_whereT"))}</b><label class="chk"><input type="radio" name="dx-mode" value="over"${S.mode === "over" ? " checked" : ""}> ${esc(t("ov_modeOver",{b:B().name}))}</label><label class="chk"><input type="radio" name="dx-mode" value="add"${S.mode === "add" ? " checked" : ""}> ${esc(t("ov_modeAdd"))}</label></div>` : ""}
      <div class="two"><label class="fld"><span>${esc(t("dx_units"))}</span><select id="dx-u">${Object.values(DXF.UNITS).map(([u, k]) => opt(u, u + " (1 = " + k + " m)", S.units)).join("")}</select></label><span></span></div>
      <label class="chk"><input type="checkbox" id="dx-walls"${S.walls ? " checked" : ""}> ${esc(t("dx_optWalls"))}</label>
      <label class="chk"><input type="checkbox" id="dx-furn"${S.furn ? " checked" : ""}> ${esc(t("dx_optFurn"))}</label>
      ${S.F.filter(F => F.on).length > 1 ? `<label class="chk" title="${esc(t("fa_btnH"))}"><input type="checkbox" id="dx-align"${S.align ? " checked" : ""}> ⇅ ${esc(t("fa_opt"))}</label>` : ""}
      <label class="chk"><input type="checkbox" id="dx-labels"${S.labels ? " checked" : ""}> ${esc(t("lx_labels"))}</label>
      ${A.blocks.length ? `<label class="chk"><input type="checkbox" id="dx-req"${S.req ? " checked" : ""}> ${esc(t("dx_optReq",{n:nOut}))}</label><label class="chk"><input type="checkbox" id="dx-devs"${S.devs ? " checked" : ""}> ${esc(t("dx_optDevs2"))}</label>
        <details class="dsec"><summary>🔌 ${esc(t("dx_blocks"))} <span class="cnt">${A.blocks.length}</span></summary><div class="dsb"><table class="t">${A.blocks.map(x => `<tr><td>${esc(x.name)}</td><td class="c">${x.n}</td><td>${kindSel(x)}</td></tr>`).join("")}</table></div></details>` : ""}
      <details class="dsec"><summary>🗂 ${esc(t("dx_layers"))} <span class="cnt">${A.layers.length}</span> <small class="muted">${esc(["wallExt","wall","door","window","roomName","area","site"].map(r => t("dxr_" + r) + " " + cnt(r)).join(" · "))}</small></summary>
        <div class="dsb scroll" style="max-height:34vh"><p class="muted small">${esc(t("dx_layersH"))}</p><table class="t">${A.layers.filter(l => l.segs + l.texts + l.refs > 0).map(l => `<tr><td>${esc(l.name)}${l.hidden ? ` <small class="muted">(${esc(t("dx_hid"))})</small>` : ""}</td><td class="c small">${l.segs || ""}</td><td class="c small">${l.texts ? "T" + l.texts : ""}</td><td>${roleSel(l)}</td></tr>`).join("")}</table></div></details>
      <p class="muted small">${esc(t("dx_note"))}</p>
      <div class="mfoot"><button class="btn" data-m="close">${esc(t("cancel"))}</button><span class="grow"></span><button class="btn pri" data-m="go">✓ ${esc(t("dx_go",{n:S.F.filter(F => F.on).length}))}</button></div>`,
      {go:() => { read(); create(); }}, {wide:true, nofocus:true});
    $$("[data-dxr],[data-dxk],#dx-u").forEach(el => el.addEventListener("change", () => { read(); if (el.id === "dx-u" || el.dataset.dxr) scan(); draw(); }));
  };
  const read = () => {
    $$("[data-dxf]").forEach(el => { const [i, k] = el.dataset.dxf.split(":"), F = S.F[+i]; if (!F) return; if (k === "on") F.on = el.checked; else if (k === "lv") F.lv = Math.round(num(el.value, F.lv)); else F.name = el.value.trim() || F.name; });
    $$("[data-dxr]").forEach(el => S.roles[el.dataset.dxr] = el.value); $$("[data-dxk]").forEach(el => S.kinds[el.dataset.dxk] = el.value);
    const u = $("#dx-u"); if (u){ const U = Object.values(DXF.UNITS).find(x => x[0] === u.value); if (U){ S.units = U[0]; S.scale = U[1]; } }
    ["walls","furn","req","devs","align","labels"].forEach(k => { const c = $("#dx-" + k); if (c) S[k] = c.checked; });
    const md = $('input[name="dx-mode"]:checked'); if (md) S.mode = md.value;
  };
  const create = async () => {
    const L = S.F.filter(F => F.on).sort((a, b) => a.lv - b.lv); if (!L.length) return;
    closeModal(); toast("⏳ " + t("dx_building"));
    const b = B(), out = [];
    for (const F of L){ const r = DXF.build(flat, {bb:F.g.bb, roles:Object.assign({}, S.roles, S.furn ? {} : Object.fromEntries(Object.entries(S.roles).filter(([, v]) => v === "furn").map(([k]) => [k, "ignore"]))), scale:S.scale, kinds:S.kinds});
      r.img = await putAsset(new Blob([r.svg], {type:"image/svg+xml"})); out.push([F, r]); }
    // floors lined up over each other (each keeps its own drawing; plan.ox / oy say where it stands)
    const SH = S.align && out.length > 1 ? floorShifts(out.map(([F, r]) => ({name:F.name, lv:F.lv, r})), x => (x.r.walls || []).map(w => [w.x1, w.y1, w.x2, w.y2])) : null;
    // the drawing as a building of its own: floors, rooms, outlets
    const src = {name:file.name, floors:[], rooms:[], devices:[]};
    out.forEach(([F, r]) => {
      const f = {id:uid("f"), name:F.name, lvl:F.lv, lv:F.lv, h:3.2}; f.plan = {wm:r.wm, hm:r.hm, img:r.img, op:100, cal:true, idf:null, walls:S.walls ? r.walls.map(w => Object.assign({id:uid("w"), src:"dxf"}, w)) : [], survey:[], items:[], src:{dxf:file.name}};
      // the drawing as editable pieces (the picture stays underneath, hidden, for comparison)
      const k0 = out.findIndex(o => o[0] === F); if (SH && SH[k0]){ f.plan.ox = SH[k0].dx; f.plan.oy = SH[k0].dy; }
      const LB = !S.labels ? [] : (r.labels || []).map(l => { const size = l.h > .3 ? 12 : 10, w = Math.round((l.text.length * size * .6 / clamp(1100 / Math.max(4, r.wm), 6, 70) + .2) * 100) / 100; return {id:uid("i"), type:"label", src:"dxf", x:Math.round((l.x - w / 2) * 100) / 100, y:Math.round((l.y - .4) * 100) / 100, w, h:.8, rot:l.rot || 0, text:l.text, size}; });
      if (r.pieces){ f.plan.vec = true; f.plan.bgop = 0; f.plan.items = r.pieces.boundaries.map(P => { const it = {id:uid("i"), type:"boundary", style:"yard", pts:P, rot:0, text:""}; DRAW.boundBox(it); return it; }); }
      f.plan.items.push(...LB);
      const R = r.rooms.map(x => { const g = x.geo, room = {id:uid("r"), name:x.name, floor:f.id, users:0, wall:S.walls ? "none" : "drywall", type:guessType(x.name), req:{}, geo:{x:g.x, y:g.y, w:g.w, h:g.h}};
        if (g.poly){ room.geo.poly = g.poly.map((v, i) => Math.round((v - (i % 2 ? g.y : g.x)) * 100) / 100); room.geo.pw = g.w; room.geo.ph = g.h; room.geo.area = x.area; } else room.geo.est = true;
        room.geo.lx = g.lx; room.geo.ly = g.ly; return normRoom(room); });
      if (r.pieces) f.plan.shapes = r.pieces.shapes.filter(o => S.furn || o.k !== "furn").map(o => Object.assign({}, o, {id:uid("s"), room:o.room !== undefined && R[o.room] ? R[o.room].id : ""}));
      src.floors.push(f); src.rooms.push(...R);
      r.outlets.forEach(o => { const rm = R.filter(x => o.x >= x.geo.x && o.x <= x.geo.x + x.geo.w && o.y >= x.geo.y && o.y <= x.geo.y + x.geo.h).sort((a, c) => a.geo.w * a.geo.h - c.geo.w * c.geo.h)[0];
        if (rm && S.req) rm.req[o.kind] = num(rm.req[o.kind]) + 1;
        const d = newDevice(o.kind, {floor:f.id, room:rm ? rm.id : ""}); d.name = ""; d.notes = o.block; setPos(d, o.x, o.y); src.devices.push(d); }); });
    // the user decides which of the devices found in the drawing come along
    if (!S.devs) src.devices = [];
    else if (src.devices.length){ const keep = await pickDrawn(src); if (keep === null) return; src.devices = keep; }
    if (S.mode === "over") return overlayPlan(src, {devs:true});
    let nD = 0;
    edit(() => {
      const below = src.floors.filter(f => f.lv < 0), above = src.floors.filter(f => f.lv >= 0); src.floors.forEach(f => { delete f.lv; });
      b.floors = [...below, ...b.floors, ...above]; b.floors.forEach((f, i) => f.lvl = i);
      b.rooms.push(...src.rooms);
      if (S.devs) src.devices.forEach(d => { d.name = autoName(b, d.kind); b.devices.push(d); nD++; });
      normBuilding(b);
      b.struct = Object.assign(b.struct || {}, {wizard:true}); st().floor = (above[0] || below[0]).id; UI.tabs.building = "plan"; UI.sel = null; UI.app = "building";
    });
    toast("✓ " + t("dx_done",{f:out.length, r:src.rooms.length, d:nD}), 6000);
  };
  draw();
}

// list of the devices found in a drawing (outlets, APs, TV, phone …): grouped by floor and kind, each one can be ticked off
function pickDrawn(src){
  return new Promise(res => {
    const D = src.devices, on = new Set(D.map(d => d.id)), rn = id => (src.rooms.find(r => r.id === id) || {}).name || "—", kinds = [...new Set(D.map(d => d.kind))];
    const draw = () => {
      const cnt = k => D.filter(d => d.kind === k), fl = src.floors.map(f => ({f, L:D.filter(d => d.floor === f.id)})).filter(x => x.L.length);
      modal(`<h3>🔌 ${esc(t("dxp_title"))}</h3><p class="muted small">${esc(t("dxp_hint",{n:D.length}))}</p>
        <div class="dxpk">${kinds.map(k => { const L = cnt(k), n = L.filter(d => on.has(d.id)).length; return `<label class="chk"><input type="checkbox" data-dxpk="${k}"${n === L.length ? " checked" : ""}${n && n < L.length ? " data-mixed=\"1\"" : ""}> <svg viewBox="0 0 48 48" width="18" height="18">${ICO[KINDS[k].icon] || ICO.box}</svg> ${esc(kindName(k))} <span class="cnt">${n}/${L.length}</span></label>`; }).join("")}</div>
        <div class="scroll" style="max-height:48vh">${fl.map(({f, L}) => `<details class="dsec"${fl.length === 1 ? " open" : ""}><summary><input type="checkbox" data-dxpf="${f.id}"${L.every(d => on.has(d.id)) ? " checked" : ""}> 🏬 ${esc(f.name)} <span class="cnt">${L.filter(d => on.has(d.id)).length}/${L.length}</span></summary>
          <div class="dsb"><table class="t">${L.slice().sort((a, c) => rn(a.room).localeCompare(rn(c.room)) || a.kind.localeCompare(c.kind)).map(d => `<tr><td style="width:28px"><input type="checkbox" data-dxpd="${d.id}"${on.has(d.id) ? " checked" : ""}></td><td><svg viewBox="0 0 48 48" width="16" height="16">${ICO[KINDS[d.kind].icon] || ICO.box}</svg> ${esc(kindName(d.kind))}</td><td>${esc(rn(d.room))}</td><td class="small muted">${esc(d.notes || "")}</td></tr>`).join("")}</table></div></details>`).join("")}</div>
        <div class="mfoot"><button class="btn" data-m="cancel">${esc(t("cancel"))}</button><button class="btn" data-m="none">${esc(t("dxp_none"))}</button><span class="grow"></span><button class="btn pri" data-m="ok">✓ ${esc(t("dxp_ok",{n:on.size}))}</button></div>`,
        {ok:() => { closeModal(); res(D.filter(d => on.has(d.id))); }, none:() => { closeModal(); res([]); }, cancel:() => { closeModal(); res(null); }}, {wide:true, nofocus:true});
      $$("[data-dxpk]").forEach(el => { if (el.dataset.mixed) el.indeterminate = true; el.addEventListener("change", () => { cnt(el.dataset.dxpk).forEach(d => el.checked ? on.add(d.id) : on.delete(d.id)); draw(); }); });
      $$("[data-dxpf]").forEach(el => { el.addEventListener("click", e => e.stopPropagation()); el.addEventListener("change", () => { D.filter(d => d.floor === el.dataset.dxpf).forEach(d => el.checked ? on.add(d.id) : on.delete(d.id)); draw(); }); });
      $$("[data-dxpd]").forEach(el => el.addEventListener("change", () => { el.checked ? on.add(el.dataset.dxpd) : on.delete(el.dataset.dxpd); const sc = $(".mfoot [data-m=ok]"); if (sc) sc.textContent = "✓ " + t("dxp_ok",{n:on.size}); }));
    };
    draw();
  });
}
/* ---------- a drawing (from DXF or from another project file) laid over the current building ----------
   Floors of the drawing are matched to the building's floors, rooms to rooms (by name; the user can change it).
   The building keeps its devices, cables, VLANs and racks; rooms get the drawn outline, devices get the drawn spots. */
// names compared without case and accents, so «FITNESS» = «Fitness», «Üst Salon» = «UST SALON», «Mətbəx» = «Metbex»
const nrm = s => String(s || "").toLocaleLowerCase("tr").replace(/ı/g, "i").replace(/ə/g, "e").normalize("NFD").replace(/[\u0300-\u036f]/g, "").replace(/[^\p{L}\p{N}]+/gu, " ").trim();
function lvOfName(n){ const x = nrm(n); if (/bodrum|zirzəmi|zirzemi|basement|podval|подвал|цокол/.test(x)) return -1; if (/zemin|ground|giriş|giris|первый/.test(x)) return 0; if (/çatı|cati|roof|çardaq/.test(x)) return 50; const m = x.match(/(\d+)/); return m ? +m[1] : null; }
async function overlayPlan(src, opts = {}){
  const b = B(), SF = src.floors.slice().sort((a, c) => (a.lv ?? a.lvl ?? 0) - (c.lv ?? c.lvl ?? 0)), DF = b.floors;
  // floors: same name, else same level number, else same position counted from the bottom
  const used = new Set(), FM = {};
  SF.forEach(f => { let d = DF.find(x => !used.has(x.id) && nrm(x.name) === nrm(f.name)); if (!d){ const lv = lvOfName(f.name); d = lv !== null && DF.find(x => !used.has(x.id) && lvOfName(x.name) === lv); }
    if (!d && SF.length === DF.length) d = DF[SF.indexOf(f)]; FM[f.id] = d ? d.id : "new"; if (d) used.add(d.id); });
  // rooms: same name on the target floor, else a name that contains the other
  const RM = {}, roomsOn = fid => b.rooms.filter(r => r.floor === fid);
  const autoRooms = () => { SF.forEach(f => { const tgt = FM[f.id], cand = tgt && tgt !== "new" && tgt !== "skip" ? roomsOn(tgt) : [], taken = new Set();
    src.rooms.filter(r => r.floor === f.id).forEach(r => { const n = nrm(r.name); let m = cand.find(x => !taken.has(x.id) && nrm(x.name) === n) || (n.length > 3 && cand.find(x => !taken.has(x.id) && nrm(x.name).length > 3 && (nrm(x.name).includes(n) || n.includes(nrm(x.name)))));
      RM[r.id] = m ? m.id : "new"; if (m) taken.add(m.id); }); }); };
  autoRooms();
  const O = {place:true, extra:false, req:true, devs:opts.devs !== false};
  const srcDevs = src.devices || [];
  const draw = () => {
    const fsel = f => `<select data-ovf="${f.id}">${opt("new", "＋ " + t("ov_newFloor"), FM[f.id])}${opt("skip", "— " + t("ov_skip"), FM[f.id])}${DF.map(x => opt(x.id, x.name, FM[f.id])).join("")}</select>`;
    const rsel = (r, fid) => `<select data-ovr="${r.id}">${opt("new", "＋ " + t("ov_newRoom"), RM[r.id])}${opt("skip", "— " + t("ov_skip"), RM[r.id])}${roomsOn(fid).map(x => opt(x.id, x.name, RM[r.id])).join("")}</select>`;
    const nMatch = Object.values(RM).filter(v => v !== "new" && v !== "skip").length;
    modal(`<h3>🧩 ${esc(t("ov_title"))}</h3><p class="muted small">${esc(t("ov_hint",{b:b.name}))}</p>
      <div class="scroll"><table class="t"><tr><th>${esc(t("ov_drawing"))}</th><th>→ ${esc(b.name)}</th><th>${esc(t("rooms"))}</th></tr>${SF.map(f => `<tr><td><b>${esc(f.name)}</b></td><td>${fsel(f)}</td><td class="c">${src.rooms.filter(r => r.floor === f.id).length}</td></tr>`).join("")}</table></div>
      ${SF.filter(f => FM[f.id] !== "skip" && FM[f.id] !== "new").map(f => `<details class="dsec"><summary>🚪 ${esc(f.name)} → ${esc((floorById(b, FM[f.id]) || {}).name)} <span class="cnt">${src.rooms.filter(r => r.floor === f.id && RM[r.id] !== "new" && RM[r.id] !== "skip").length}/${src.rooms.filter(r => r.floor === f.id).length}</span></summary>
        <div class="dsb scroll" style="max-height:32vh"><table class="t">${src.rooms.filter(r => r.floor === f.id).map(r => `<tr><td>${esc(r.name)}</td><td>${rsel(r, FM[f.id])}</td></tr>`).join("")}</table></div></details>`).join("")}
      <p class="small">${esc(t("ov_sum",{m:nMatch, n:Object.keys(RM).length - nMatch}))}</p>
      <label class="chk"><input type="checkbox" id="ov-place"${O.place ? " checked" : ""}> ${esc(t("ov_place"))}</label>
      <label class="chk"><input type="checkbox" id="ov-req"${O.req ? " checked" : ""}> ${esc(t("ov_req"))}</label>
      ${srcDevs.length ? `<label class="chk"><input type="checkbox" id="ov-extra"${O.extra ? " checked" : ""}> ${esc(t("ov_extra"))}</label>` : ""}
      <p class="muted small">${esc(t("ov_keep"))}</p>
      <div class="mfoot"><button class="btn" data-m="close">${esc(t("cancel"))}</button><span class="grow"></span><button class="btn pri" data-m="go">✓ ${esc(t("ov_go"))}</button></div>`, {go:() => { read(); apply(); }}, {wide:true, nofocus:true});
    $$("[data-ovf]").forEach(el => el.addEventListener("change", () => { read(); autoRooms(); draw(); }));
  };
  const read = () => { $$("[data-ovf]").forEach(el => { FM[el.dataset.ovf] = el.value; }); $$("[data-ovr]").forEach(el => { RM[el.dataset.ovr] = el.value; });
    ["place","req","extra"].forEach(k => { const c = $("#ov-" + k); if (c) O[k] = c.checked; }); };
  const apply = () => {
    closeModal(); let nPlaced = 0, nNew = 0, nRooms = 0;
    edit(() => {
      const fmap = {}, rmap = {};
      SF.forEach(f => { const tgt = FM[f.id]; if (tgt === "skip") return;
        let d;
        if (tgt === "new"){ d = {id:uid("f"), name:f.name, lvl:0, h:f.h || 3.2, plan:clone(f.plan)}; const lv = f.lv ?? lvOfName(f.name) ?? 0; if (lv < 0) b.floors.unshift(d); else b.floors.push(d); }
        else { d = floorById(b, tgt); const old = d.plan;
          // devices already on this floor keep their place relative to their room; others wait in "not on the plan"
          const oldGeo = {}; b.rooms.filter(r => r.floor === d.id && r.geo).forEach(r => { oldGeo[r.id] = clone(r.geo); });
          d.plan = Object.assign({}, old, {wm:f.plan.wm, hm:f.plan.hm, img:f.plan.img, op:f.plan.op ?? 100, cal:true, walls:clone(f.plan.walls || []), items:[...(f.plan.items || [])], shapes:clone(f.plan.shapes || []), vec:!!f.plan.vec, bgop:f.plan.bgop, src:f.plan.src || null, idf:old.idf || null, survey:[]});
          d.__old = oldGeo; }
        fmap[f.id] = d; });
      // rooms
      src.rooms.forEach(r => { const d = fmap[r.floor]; if (!d) return; const tgt = RM[r.id] || "new";
        if (tgt === "skip") return;
        if (tgt === "new"){ const c = Object.assign(clone(r), {id:uid("r"), floor:d.id}); b.rooms.push(c); rmap[r.id] = c; nRooms++; return; }
        const x = roomById(b, tgt); if (!x) return; x.geo = clone(r.geo); x.wall = r.wall || x.wall; if (!x.type || x.type === "office") x.type = r.type || x.type;
        if (O.req && r.req && !Object.values(x.req || {}).some(v => num(v))) x.req = clone(r.req);
        rmap[r.id] = x; nRooms++; });
      // drawing pieces that belong to a room follow it to the room it was matched with
      Object.values(fmap).forEach(d => (d.plan.shapes || []).forEach(o => { if (o.room) o.room = rmap[o.room] ? rmap[o.room].id : ""; }));
      // rooms of a re-drawn floor that got no outline: their old box no longer fits the drawing
      Object.values(fmap).forEach(d => { if (!d.__old) return; const matched = new Set(Object.values(rmap).map(x => x.id)); b.rooms.filter(x => x.floor === d.id && !matched.has(x.id) && d.__old[x.id]).forEach(x => { delete x.geo; }); });
      // devices already in the building
      Object.values(fmap).forEach(d => {
        const devs = b.devices.filter(x => (x.floor === d.id || (x.room && (roomById(b, x.room) || {}).floor === d.id)) && !x.rack);
        devs.forEach(x => { const p = posOf(x), rm = x.room && roomById(b, x.room), og = d.__old && d.__old[x.room];
          if (p && rm && rm.geo && og && og.w && og.h){ setPos(x, rm.geo.x + (p.x - og.x) / og.w * rm.geo.w, rm.geo.y + (p.y - og.y) / og.h * rm.geo.h); }
          else if (p && d.__old) clearPos(x); });
        delete d.__old; });
      // drawn spots → existing devices of the same room and kind (a data outlet spot also takes a PC, printer … of that room)
      const left = [];
      if (O.place){ const ENDS = ["pc","printer","workstation","laptop","phone","tv","monitor","touch","iot"];
        srcDevs.forEach(sd => { const x = rmap[sd.room]; if (!x) return left.push(sd); const p = posOf(sd);
          const cand = b.devices.filter(q => q.room === x.id && !q.rack && !posOf(q));
          const m = cand.find(q => q.kind === sd.kind) || (sd.kind === "outlet" && cand.find(q => ENDS.includes(q.kind)));
          if (m && p){ setPos(m, p.x, p.y); m.floor = x.floor; nPlaced++; } else left.push(sd); }); }
      else left.push(...srcDevs);
      if (O.extra) left.forEach(sd => { const x = rmap[sd.room], d = fmap[sd.floor]; if (!d) return; const c = Object.assign(clone(sd), {id:uid("d"), floor:d.id, room:x ? x.id : "", status:"planned"}); c.name = autoName(b, c.kind); b.devices.push(c); nNew++; });
      b.floors.forEach((f, i) => f.lvl = i); normBuilding(b);
      b.struct = Object.assign(b.struct || {}, {wizard:true}); const first = Object.values(fmap)[0]; if (first) st().floor = first.id; UI.app = "building"; UI.tabs.building = "plan"; UI.sel = null;
    });
    toast("✓ " + t("ov_done",{r:nRooms, p:nPlaced, n:nNew}), 7000);
  };
  draw();
}

registerApp({
  id:"building", name:"app_building", desc:"app_building_d", docName:"doc_building", color:"#6a3aa0",
  glyph:`<path d="M12 38V14l12-6 12 6v24z" fill="#fff"/><path d="M17 18h4v4h-4zM27 18h4v4h-4zM17 26h4v4h-4zM27 26h4v4h-4z" fill="#6a3aa0"/><path d="M21 38v-6h6v6" fill="#ffb703"/>`,
  tabs:[
    {id:"plan", label:"bd_tabPlan", icon:"🗺", palette, render:planView,
      tour:() => [{sel:"#appsw", title:t("tShellT1"), text:t("tShell1")}, {sel:".bfloors", title:t("bd_tT1"), text:t("bd_t1")}, {sel:"#pal .psec", title:t("bd_tT2"), text:t("bd_t2")}, {sel:"svg.bplan", title:t("bd_tT3"), text:t("bd_t3")}, {sel:'[data-tab="struct"]', title:t("bd_tT4"), text:t("bd_t4")}, tip('#pal [data-ba="wizard"]', "tp_bdWiz"), tip('#pal [data-ba="dxf"]', "tp_bdDxf"), tip('[data-ba="mergeDup"]', "tp_bdMerge"), TIPS.warn(), TIPS.places(), {sel:"#btabs", title:t("tShellT2"), text:t("tShell2")}]},
    {id:"struct", label:"bd_tabStruct", icon:"🏢", render:structView, tour:() => [tip(".btree", "tp_bdTree")]},
    {id:"req", label:"bd_tabReq", icon:"📋", render:reqView, tour:() => [tip('[data-tp="req"]', "tp_bdReq"), tip('[data-ba="createAll"]', "tp_bdCreate")]},
    docTab("building", docBody)
  ],
  actions(tab){ return [{id:"wiz", icon:"🧭", label:"bd_wizard", fn:wizard}, {id:"addFloor", icon:"＋", label:"floorNew", fn:() => act("addFloor")}, {id:"places", icon:"🏢", label:"places", fn:() => openPlaces()}]; },
  drawer, onField, onDrawerAct, onKey(e, tab){ if (tab.id === "plan") onKey(e); },
  onEsc(){ if (poly){ finishPoly(true); return true; } if (place){ place = null; render(); return true; } return false; },
  exports(){ return [{icon:"▦", label:t("bd_reqT") + " (CSV)", fn:() => act("reqCsv")}]; },
  reveal(s){ if (!s) return; const b = B(); if (s.type === "dev"){ const d = devById(b, s.id); if (d && devFloor(b, d)) st().floor = devFloor(b, d); } if (s.type === "room"){ const r = roomById(b, s.id); if (r) st().floor = r.floor; } UI.tabs.building = "plan"; render(); },
  guide:() => [[t("bd_g1h"), t("bd_g1")], [t("bd_g2h"), t("bd_g2")], [t("bd_g3h"), t("bd_g3")], [t("bd_g4h"), t("bd_g4")]]
});
APPS.building.init = wire;
// a building without floors opens the set-up once, the first time the app is shown for it
APPS.building.afterRender = () => { const b = B(); if (b.floors.length || b.devices.length || b.racks.length || (b.struct && b.struct.wizard) || !store.settings.setupDone || !$("#modal").hidden || document.querySelector(".tour")) return; b.struct = Object.assign(b.struct || {}, {wizard:true}); persist(); setTimeout(wizard, 300); };
window.BLD = {siteWalls, siteUsed, sitePage, wizard, createMissing, posOf, dxfImport, guessType, planSvg, overlayPlan, palette, planView, drawer, onField, onDrawerAct, onKey};
})();
