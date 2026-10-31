/*! NetWorkKing — © 2026 Ulvi Badalov. Bütün hüquqlar qorunur / All rights reserved. Proprietary — see LICENSE. */
// Wi-Fi Plan: predictive Wi-Fi design on the building's floor plans (ported from Wolf Suite v2 Wi-Fi Plan).
// Walls with per-band losses, doors / windows, scale calibration, multi-band AP radios, RSSI / SNR / secondary coverage /
// AP count / co-channel / data-rate / best-AP / pass views, requirement profiles, automatic channel plan, floor-to-floor
// bleed, IDF cable lengths, PoE budgets, client load, site-survey comparison, BOM and exports.
// Every AP is a shared building device (kind "ap"); floors and rooms are the building's floors and rooms,
// so the same AP shows up in Topology, Port Map, Rack and the inventory.
"use strict";
(function(){
const gt = window.t;
// Wi-Fi strings are stored with a "wf_" prefix; fall back to the shared strings.
const t = (k, v) => { const r = gt("wf_" + k, v); return r === "wf_" + k ? gt(k, v) : r; };
const PW = 740;
const BANDS = ["2.4", "5", "6"];
const BI = {"2.4":0, "5":1, "6":2};
const BFREQ = {"2.4":2437, "5":5500, "6":6500};
// Typical attenuation per crossing in dB for 2.4 / 5 / 6 GHz (order of magnitude from ITU-R P.2040 and vendor survey tools).
const MAT = {none:[0,0,0], cubicle:[1,2,2], glass:[2,3,4], drywall:[3,4,5], wood:[3,4,5], door:[3,4,5], brick:[6,10,12], block:[8,12,14],
  concrete:[12,16,20], rcon:[18,25,30], lowe:[20,25,28], metaldoor:[15,20,24], metal:[26,32,36], elevator:[30,35,40]};
const MSTYLE = {none:"stroke=\"none\"", cubicle:'stroke="#9aa3b5" stroke-width="1.2" stroke-dasharray="3 2"', glass:'stroke="#5b9bd5" stroke-width="2" stroke-dasharray="6 3"',
  drywall:'stroke="#3a3f4b" stroke-width="1.8"', wood:'stroke="#9a6a32" stroke-width="2.2"', door:'stroke="#b0702a" stroke-width="3"', brick:'stroke="#8b3a2b" stroke-width="2.6"',
  block:'stroke="#5d4b3b" stroke-width="2.8"', concrete:'stroke="#1d2433" stroke-width="3.2"', rcon:'stroke="#000" stroke-width="4"', lowe:'stroke="#2e7d6b" stroke-width="2.6" stroke-dasharray="7 2"',
  metaldoor:'stroke="#6b7280" stroke-width="3.4"', metal:'stroke="#4b5563" stroke-width="4"', elevator:'stroke="#374151" stroke-width="4.4"'};
const FC = {blue:["#d9e6fb","#1f3f8f"], green:["#dcf0d8","#2a7a35"], orange:["#fcd9b6","#c4601a"], purple:["#eadcf7","#6a3aa0"], gray:["#e6e8ec","#4b5262"], teal:["#d5f0ef","#11706f"]};
const PROF = {
  basic:{rssi:-72, snr:15, sec:"", cnt:1, cntR:-75, cci:3, cover:90},
  data:{rssi:-67, snr:25, sec:"", cnt:1, cntR:-67, cci:2, cover:95},
  voip:{rssi:-67, snr:25, sec:-67, cnt:2, cntR:-67, cci:1, cover:98},
  rtls:{rssi:-67, snr:20, sec:-75, cnt:3, cntR:-75, cci:2, cover:95}
};
const VIEWS = ["rssi","snr","sec","cnt","cci","rate","best","pass"];
const CH24 = [1, 6, 11];
const CH5N = [36,40,44,48,149,153,157,161,165], CH5D = [52,56,60,64,100,104,108,112,116,120,124,128,132,136,140,144];
const MCS_SNR = [2,5,9,11,15,18,20,25,29,31,34,37];                       // SNR (dB) needed for HE-MCS 0…11
const MCS_R20 = [8.6,17.2,25.8,34.4,51.6,68.8,77.4,86,103.2,114.7,129,143.4]; // HE, 20 MHz, 1 SS, 0.8 µs GI (Mbps)
const WFAC = {20:1, 40:2, 80:4.19, 160:8.38};
const APCOL = ["#1f6fd6","#d0453b","#2a9d3a","#8e44ad","#e67e22","#16a3a3","#c0392b","#7f8c8d","#b7950b","#2c3e50","#e84393","#00a8ff"];
let drag = null, tool = "select", pend = null, mline = null, placeId = null;

/* ---------- settings stored on the building (b.wifi) ---------- */
function wset(b){
  const w = b.wifi = b.wifi && typeof b.wifi === "object" ? b.wifi : {};
  w.cfg = Object.assign({n:3, floorH:3.5, clientH:1, cg:0, nf:{"2.4":-92, "5":-95, "6":-95}, fl:{"2.4":14, "5":18, "6":22}, prof:"data", pc:Object.assign({}, PROF.data),
    dfs:false, w5:40, w6:80, cpa:50, dpu:1.5, css:2, vert:4, slack:3}, w.cfg || {});
  w.cfg.nf = Object.assign({"2.4":-92, "5":-95, "6":-95}, w.cfg.nf || {}); w.cfg.fl = Object.assign({"2.4":14, "5":18, "6":22}, w.cfg.fl || {});
  w.view = Object.assign({band:"5", mode:"rssi", op:70, chan:true, cable:false, survey:true}, w.view || {});
  w.ssid = Array.isArray(w.ssid) ? w.ssid : []; w.notes = Array.isArray(w.notes) ? w.notes : []; w.equip = Array.isArray(w.equip) ? w.equip : [];
  return w;
}
/* ---------- working copy ("facade") of the building in the shape the planner uses ----------
   floors (top floor first) with rooms (b.rooms with r.geo), walls, survey points, IDF; aps = placed AP devices.
   Built on every render; changes go through commit(), which writes them back to the building. */
let FCD = null;
// VLANs an AP carries, as set elsewhere: the switch port it is cabled to (Port Map: access VLAN, or trunk native + allowed), else the device VLAN.
function portVlans(b, d){
  const up = window.PM ? PM.upstream(b, d) : {}, c = up.sw && up.sw.pcfg && up.sw.pcfg[up.p], vid = id => (vlanById(b, id) || {}).vid, out = [];
  if (c){ if (c.mode === "trunk"){ if (c.native) out.push(vid(c.native)); String(c.allowed || "").split(/[\s,;]+/).filter(Boolean).forEach(x => out.push(x)); } else if (c.vlan) out.push(vid(c.vlan)); }
  if (!out.length && d.vlan) out.push(vid(d.vlan));
  return [...new Set(out.filter(Boolean))].join(",");
}
function apIn(b, d){
  const up = window.PM ? PM.upstream(b, d) : {};
  const a = {id:d.id, name:d.name, floor:d.floor, x:num(d.ap.x), y:num(d.ap.y), h:num(d.ap.h, 3), mount:d.ap.mount || "ceiling", status:d.status, radios:d.ap.radios,
    model:[d.brand, d.model].filter(Boolean).join(" "), ip:d.ip, mac:d.mac, serial:d.serial, note:d.notes, cable:d.ap.cable || "", vlans:d.ap.vlans || portVlans(b, d), vlansOwn:d.ap.vlans || "",
    sw:up.sw ? devLabel(up.sw) : "", swId:up.sw ? up.sw.id : "", port:up.p || ""};
  Object.defineProperty(a, "__d", {value:d, enumerable:false, writable:true});
  return a;
}
function syncIn(){
  const b = B(), W = wset(b), n = b.floors.length;
  // the site plan («Çevrə») comes last, after the lowest floor; it is not stacked with the floors (no signal through it)
  const floors = b.floors.slice().reverse().concat([siteOf(b)]).map((sf, i) => { const p = sf.plan;
    return {id:sf.id, name:sf.name, desc:p.desc || "", color:p.color || (sf.id === OUT_FLOOR ? "green" : Object.keys(FC)[(n - 1 - i) % 6]), wm:clamp(num(p.wm, 40), 2, 2000), hm:clamp(num(p.hm, 14), 2, Math.min(2000, clamp(num(p.wm, 40), 2, 2000) * 20)),   /* depth ≤ 20 × width: the plan canvas stays drawable */ img:p.img || null, op:p.op ?? 60, idf:p.idf || null, ox:num(p.ox, 0), oy:num(p.oy, 0),
      walls:p.walls, survey:p.survey, calibrated:!!p.cal,
      rooms:b.rooms.filter(r => r.floor === sf.id && r.geo).map(r => { const o = {id:r.id, label:r.name, wall:r.wall || "drywall", users:num(r.users), x:num(r.geo.x), y:num(r.geo.y), w:num(r.geo.w, 1), h:num(r.geo.h, 1)};
        // outline and name position drawn from a DXF drawing (kept as they are; only x / y / w / h are edited here)
        ["poly","pw","ph","lx","ly"].forEach(k => { if (r.geo[k] !== undefined) Object.defineProperty(o, k, {value:r.geo[k], enumerable:false, writable:true}); }); return o; })}; });
  // the Building plan of each floor (an edited drawing is shown instead of the picture)
  floors.forEach(f => { const sf = planFloor(b, f.id); Object.defineProperty(f, "pv", {value:sf && sf.plan, enumerable:false, writable:true}); });
  const fids = new Set(floors.map(f => f.id));
  const aps = b.devices.filter(d => d.kind === "ap" && d.ap && d.ap.x !== null && d.ap.x !== undefined && d.ap.x !== "" && fids.has(d.floor)).map(d => apIn(b, d));
  FCD = {b, apIds:new Set(aps.map(a => a.id)), roomIds:new Set(floors.flatMap(f => f.rooms.map(r => r.id))),
    d:{name:b.name, floors, aps, cfg:W.cfg, view:W.view, tables:{ssid:W.ssid}, notes:W.notes, equip:W.equip}};
  return FCD.d;
}
function D(){ if (!FCD || FCD.b !== B()) syncIn(); return FCD.d; }
function syncOut(){
  if (!FCD) return; const b = FCD.b, d = FCD.d, W = wset(b);
  W.cfg = d.cfg; W.view = d.view; W.ssid = d.tables.ssid; W.notes = d.notes; W.equip = d.equip;
  const byId = new Map(b.floors.map(f => [f.id, f])), out = [];
  d.floors.slice().reverse().forEach(ff => { const site = ff.id === OUT_FLOOR, sf = site ? siteOf(b) : byId.get(ff.id) || {id:ff.id, name:ff.name, lvl:b.floors.length};
    sf.name = String(ff.name || "").trim() || sf.name;
    sf.plan = Object.assign(sf.plan || {}, {desc:ff.desc, color:ff.color, wm:ff.wm, hm:ff.hm, img:ff.img, op:ff.op, idf:ff.idf, walls:ff.walls, survey:ff.survey, cal:!!ff.calibrated});
    if (!site) out.push(sf); byId.delete(ff.id);
    ff.rooms.forEach(r => { let sr = roomById(b, r.id); if (!sr){ sr = {id:r.id}; b.rooms.push(sr); }
      sr.name = String(r.label || "").split("\n").join(" ").trim() || t("newRoom"); sr.floor = ff.id; sr.wall = r.wall; sr.users = num(r.users); sr.geo = Object.assign(sr.geo || {}, {x:r.x, y:r.y, w:r.w, h:r.h}); if (r.lx !== undefined){ sr.geo.lx = r.lx; sr.geo.ly = r.ly; } }); });
  byId.forEach(sf => { b.rooms.forEach(r => { if (r.floor === sf.id) r.floor = ""; }); b.devices.forEach(x => { if (x.floor === sf.id){ x.floor = ""; if (x.kind === "ap") x.ap.x = x.ap.y = null; } }); });
  b.floors = out;
  const seenR = new Set(d.floors.flatMap(f => f.rooms.map(r => r.id)));
  FCD.roomIds.forEach(id => { if (seenR.has(id)) return; const r = roomById(b, id); if (!r) return;
    if (b.devices.some(x => x.room === id)) delete r.geo; else b.rooms = b.rooms.filter(x => x.id !== id); });
  const seenA = new Set();
  d.aps.forEach(a => { seenA.add(a.id); let dv = devById(b, a.id);
    if (!dv){ const tpl = a.__tpl && devById(b, a.__tpl);
      dv = newDevice("ap", {id:a.id, name:a.name});
      if (tpl){ ["brand","model","cat"].forEach(k => { if (tpl[k] !== undefined) dv[k] = clone(tpl[k]); }); dv.params = clone(tpl.params); dv.ap.std = tpl.ap.std; dv.ap.maxClients = tpl.ap.maxClients; }
      b.devices.push(dv); }
    dv.name = a.name; dv.floor = a.floor; dv.status = a.status; dv.notes = a.note || ""; dv.ip = a.ip || ""; dv.mac = a.mac || ""; dv.serial = a.serial || "";
    Object.assign(dv.ap, {x:a.x, y:a.y, h:a.h, mount:a.mount, cable:a.cable, vlans:a.vlansOwn !== undefined ? a.vlansOwn : a.vlans, radios:a.radios});
    a.__d = dv; });
  const gone = [...FCD.apIds].filter(id => !seenA.has(id));
  if (gone.length) removeDevices(b, gone);
}
// Change made on the working copy: undo point, write back, save, redraw.
function commit(fn){ pushUndo(); fn(); syncOut(); normBuilding(B()); persist(); render(); }
function save(){ syncOut(); persist(); }

/* ---------- AP model (from the device / catalog record) ---------- */
const devOf = a => a.__d || devById(B(), a.id);
function MOD(a){
  const dv = devOf(a), R = a.radios || {}, b = {};
  BANDS.forEach(k => { const x = R[k]; if (x && !x.none) b[k] = [num(x.maxTx, 20), num(x.gain, 3)]; });
  return {v:dv ? dv.brand : "", std:dv && dv.ap.std || "", b, poe:num(dv && dv.params.poeIn), cls:dv && dv.params.poeStd || "", cl:num(dv && dv.ap.maxClients)};
}
const radio = (a, b) => (a.radios && a.radios[b]) || {on:false};
const radioOn = (a, b) => radio(a, b).on && !radio(a, b).none && a.status !== "removed";
const txOf = (a, b) => num(radio(a, b).tx, 17);
const gainOf = (a, b) => num(radio(a, b).gain, 3);
const fspl1 = b => 20 * Math.log10(BFREQ[b]) - 27.55;
function prof(d){ return d.cfg.prof === "custom" ? d.cfg.pc : PROF[d.cfg.prof] || PROF.data; }

/* ---------- channels ---------- */
function span(b, ch, w){
  if (b === "2.4"){ const c = 2407 + 5 * ch; return [c - 11, c + 11]; }
  const n = Math.max(1, w / 20);
  if (b === "5"){ const base = ch >= 149 ? 149 : 36, st = base + Math.floor((ch - base) / (4 * n)) * 4 * n, lo = 5000 + 5 * st - 10; return [lo, lo + w]; }
  const st = 1 + Math.floor((ch - 1) / (4 * n)) * 4 * n, lo = 5950 + 5 * st - 10; return [lo, lo + w];
}
const overlap = (p, q) => p[0] < q[1] && q[0] < p[1];
const rspan = (a, b) => { const r = radio(a, b); return span(b, num(r.ch, 1), b === "2.4" ? 20 : num(r.w, 20)); };
const isDFS = ch => ch >= 52 && ch <= 144;
function chList(b, w, dfs){
  if (b === "2.4") return CH24;
  const n = Math.max(1, w / 20);
  if (b === "5"){ const all = [...CH5N, ...(dfs ? CH5D : [])].sort((x, y) => x - y), set = new Set(all), out = [];
    all.forEach(ch => { const base = ch >= 149 ? 149 : 36, st = base + Math.floor((ch - base) / (4 * n)) * 4 * n; if (st !== ch) return;
      for (let i = 0; i < n; i++) if (!set.has(st + 4 * i)) return; if (n > 1 && st === 165) return; out.push(st); });
    return out; }
  const out = []; for (let st = 1; st + 4 * (n - 1) <= 233; st += 4 * n){ const psc = [...Array(n)].map((_, i) => st + 4 * i).find(c => (c - 5) % 16 === 0); out.push(psc || st); }
  return out;
}

/* ---------- lookup ---------- */
const S = () => UI.sel ? UI.sel.id : null;
function setSel(id){ if (!id){ UI.sel = null; return; } const d = D(); UI.sel = {type:d.aps.some(a => a.id === id) || devById(B(), id) ? "dev" : "wf", id}; }
function find(d, id){
  if (!id || !d) return null;
  for (const f of d.floors){ if (f.id === id) return {kind:"floor", o:f, f};
    const r = f.rooms.find(x => x.id === id); if (r) return {kind:"room", o:r, f};
    const w = f.walls.find(x => x.id === id); if (w) return {kind:"wall", o:w, f};
    const s = f.survey.find(x => x.id === id); if (s) return {kind:"survey", o:s, f}; }
  const a = d.aps.find(x => x.id === id); if (a) return {kind:"ap", o:a, f:d.floors.find(f => f.id === a.floor)};
  return null;
}
const fName = f => f ? lines(f.name).join(" ").replace(/\s+/g, " ") : "—";
const fShort = fName;
const rLabel = r => lines(r.label).join(" ");

/* ---------- propagation ---------- */
function wallsOf(f, b){
  const W = [], i = BI[b];
  f.rooms.forEach(r => { const L = (MAT[r.wall] || MAT.drywall)[i]; if (!L) return;
    W.push([r.x, r.y, r.x + r.w, r.y, L, 0], [r.x + r.w, r.y, r.x + r.w, r.y + r.h, L, 0], [r.x, r.y + r.h, r.x + r.w, r.y + r.h, L, 0], [r.x, r.y, r.x, r.y + r.h, L, 0]); });
  // a bent wall (drawn in Building structure) counts as 8 short straight pieces along its arc
  f.walls.forEach(w => { const L = (MAT[w.mat] || MAT.drywall)[i], o = w.kind === "wall" ? 0 : 1;
    if (!num(w.bend)) return W.push([w.x1, w.y1, w.x2, w.y2, L, o]); let a = DRAW.wallPt(w, 0); for (let k = 1; k <= 8; k++){ const q = DRAW.wallPt(w, k / 8); W.push([a.x, a.y, q.x, q.y, L, o]); a = q; } });
  return W;
}
// Sum of wall losses along a ray; a door / window lying on a wall replaces that wall's loss at the same point.
function wallLoss(W, ax, ay, bx, by){
  const hits = [], rx = bx - ax, ry = by - ay;
  for (let i = 0; i < W.length; i++){
    const w = W[i], x1 = w[0], y1 = w[1], x2 = w[2], y2 = w[3];
    if (Math.max(x1, x2) < Math.min(ax, bx) - .01 || Math.min(x1, x2) > Math.max(ax, bx) + .01 || Math.max(y1, y2) < Math.min(ay, by) - .01 || Math.min(y1, y2) > Math.max(ay, by) + .01) continue;
    const sx = x2 - x1, sy = y2 - y1, den = rx * sy - ry * sx; if (Math.abs(den) < 1e-9) continue;
    const t1 = ((x1 - ax) * sy - (y1 - ay) * sx) / den, u = ((x1 - ax) * ry - (y1 - ay) * rx) / den;
    if (t1 > 1e-4 && t1 < 1 - 1e-4 && u >= -1e-4 && u <= 1 + 1e-4) hits.push([t1, w[4], w[5]]);
  }
  if (!hits.length) return 0;
  hits.sort((p, q) => p[0] - q[0]);
  let sum = 0, i = 0;
  while (i < hits.length){ let j = i, best = 0, pri = -1; const t0 = hits[i][0];
    while (j < hits.length && hits[j][0] - t0 < .004){ const [, L, p] = hits[j]; if (p > pri){ pri = p; best = L; } else if (p === pri && L > best) best = L; j++; }
    sum += best; i = j; }
  return sum;
}
// APs that can be heard on floor f (same floor and up to two floors above / below).
const apart = (A, C) => A !== C && (A === OUT_FLOOR || C === OUT_FLOOR);   // the site plan and a floor do not hear each other
function apsFor(d, f, b){
  const fi = d.floors.indexOf(f), out = [];
  d.aps.forEach(a => { if (!radioOn(a, b)) return; const fj = d.floors.findIndex(x => x.id === a.floor); if (fj < 0 || apart(a.floor, f.id)) return; const k = Math.abs(fj - fi); if (k > 2) return;
    const h = num(a.h, 3), ch = d.cfg.clientH, dz = k === 0 ? h - ch : fj < fi ? k * d.cfg.floorH + h - ch : k * d.cfg.floorH - h + ch;
    // floors lined up in the Building app: an AP on another floor stands where that floor lies under / over this one
    const g = d.floors[fj], ox = k ? num(g.ox, 0) - num(f.ox, 0) : 0, oy = k ? num(g.oy, 0) - num(f.oy, 0) : 0;
    out.push({a, k, ox, oy, dz:Math.abs(dz), eirp:txOf(a, b) + gainOf(a, b), sp:rspan(a, b), w:b === "2.4" ? 20 : num(radio(a, b).w, 20)}); });
  return out;
}
function sigAt(d, b, A, x, y, walls){
  const dist = Math.max(1, Math.hypot(x - A.a.x - (A.ox || 0), y - A.a.y - (A.oy || 0), A.dz));
  let r = A.eirp + d.cfg.cg - fspl1(b) - 10 * d.cfg.n * Math.log10(dist);
  if (A.k) r -= A.k * num(d.cfg.fl[b], 18); else if (walls.length) r -= wallLoss(walls, A.a.x, A.a.y, x, y);
  return r;
}
const HCACHE = new Map();
function heat(d, f, b, step){
  const s = PW / f.wm, H = Math.round(f.hm * s), A = apsFor(d, f, b);
  const key = JSON.stringify([b, step, f.wm, f.hm, f.rooms.map(r => [r.x, r.y, r.w, r.h, r.wall]), f.walls.map(w => [w.x1, w.y1, w.x2, w.y2, w.mat, w.kind, w.bend]), A.map(q => [q.a.id, q.a.x, q.a.y, q.k, q.dz, q.eirp, q.sp, q.ox, q.oy]), d.cfg.n, d.cfg.cg, d.cfg.fl[b]]);
  if (HCACHE.has(key)) return HCACHE.get(key);
  // memory: at most ~4 million signal values per map (many APs on a huge floor get a coarser grid instead of a crash)
  while (Math.ceil(PW / step) * Math.ceil(H / step) * Math.max(1, A.length) > 4e6) step *= 1.4;
  const cols = Math.ceil(PW / step), rows = Math.ceil(H / step), nA = A.length, R = new Float32Array(cols * rows * Math.max(1, nA)).fill(-200);
  const walls = wallsOf(f, b);
  for (let j = 0; j < rows; j++) for (let i = 0; i < cols; i++){
    const mx = (i + .5) * step / s, my = (j + .5) * step / s, o = (j * cols + i) * nA;
    for (let q = 0; q < nA; q++) R[o + q] = sigAt(d, b, A[q], mx, my, walls);
  }
  const res = {cols, rows, step, s, A, nA, R};
  if (HCACHE.size > 12) HCACHE.clear();
  HCACHE.set(key, res); return res;
}
function cellInfo(d, h, k, b, P){
  const o = k * h.nA; let best = -200, bi = -1, sec = -200, cnt = 0;
  for (let q = 0; q < h.nA; q++){ const v = h.R[o + q]; if (v > best){ sec = best; best = v; bi = q; } else if (v > sec) sec = v; if (v >= P.cntR) cnt++; }
  let cci = 0;
  if (bi >= 0) for (let q = 0; q < h.nA; q++) if (q !== bi && h.R[o + q] >= -82 && overlap(h.A[q].sp, h.A[bi].sp)) cci++;
  const snr = best - num(d.cfg.nf[b], -95);
  const pass = best >= P.rssi && snr >= P.snr && (P.sec === "" || P.sec === undefined || sec >= num(P.sec)) && cnt >= num(P.cnt, 1) && cci <= num(P.cci, 9);
  return {best, bi, sec, cnt, cci, snr, pass};
}
function rateOf(d, snr, w){ const eff = snr - 10 * Math.log10(w / 20); let m = -1; for (let i = 0; i < MCS_SNR.length; i++) if (eff >= MCS_SNR[i]) m = i; return m < 0 ? 0 : MCS_R20[m] * (WFAC[w] || 1) * num(d.cfg.css, 2); }
const RSTOPS = [[-40,[21,94,190]],[-50,[47,180,232]],[-60,[124,201,106]],[-67,[200,224,90]],[-72,[240,226,92]],[-80,[245,160,60]],[-86,[230,90,60]]];
function grad(stops, v, floor){
  if (v < floor) return null;
  if (v >= stops[0][0]) return [...stops[0][1], 175];
  for (let i = 0; i < stops.length - 1; i++){ const [a, ca] = stops[i], [b2, cb] = stops[i+1];
    if (v <= a && v >= b2){ const k = (a - v) / (a - b2); return [0,1,2].map(j => Math.round(ca[j] + (cb[j] - ca[j]) * k)).concat(175); } }
  const L = stops[stops.length - 1]; return [...L[1], 120];
}
const hex = c => [1,3,5].map(i => parseInt(c.slice(i, i + 2), 16));
const SSTOPS = [[40,[21,94,190]],[30,[47,180,232]],[25,[124,201,106]],[20,[240,226,92]],[15,[245,160,60]],[10,[230,90,60]]];
const RATESTOPS = [[1000,[21,94,190]],[600,[47,180,232]],[300,[124,201,106]],[150,[240,226,92]],[50,[245,160,60]],[10,[230,90,60]]];
function colorFor(d, view, c, h){
  if (c.bi < 0 || c.best < -90) return null;
  switch (view){
    case "snr": return grad(SSTOPS, c.snr, 5);
    case "sec": return c.sec > -200 ? grad(RSTOPS, c.sec, -88) : null;
    case "cnt": return c.cnt >= 3 ? [42,160,70,170] : c.cnt === 2 ? [150,205,90,170] : c.cnt === 1 ? [245,205,70,170] : [220,80,60,110];
    case "cci": return c.best < -82 ? null : c.cci === 0 ? [42,160,70,165] : c.cci === 1 ? [245,205,70,170] : c.cci === 2 ? [245,150,60,175] : [215,55,45,180];
    case "rate": { const r = rateOf(d, c.snr, h.A[c.bi].w); return r ? grad(RATESTOPS, r, 1) : null; }
    case "best": { if (c.best < -80) return null; const q = Math.max(0, d.aps.indexOf(h.A[c.bi] && h.A[c.bi].a)); return [...hex(APCOL[q % APCOL.length]), c.best >= -67 ? 120 : 70]; }
    case "pass": return c.pass ? [42,160,70,130] : [215,55,45,130];
    default: return grad(RSTOPS, c.best, -88);
  }
}
function evalFloor(d, f, b){
  const h = heat(d, f, b, 8), P = prof(d), n = h.cols * h.rows; if (!h.nA) return {pct:0, rooms:{}, n:0, avg:null};
  let ok = 0, sum = 0; const rc = {};
  const rooms = f.rooms.map(r => ({r, i0:Math.floor(r.x * h.s / h.step), i1:Math.ceil((r.x + r.w) * h.s / h.step), j0:Math.floor(r.y * h.s / h.step), j1:Math.ceil((r.y + r.h) * h.s / h.step)}));
  for (let k = 0; k < n; k++){ const c = cellInfo(d, h, k, b, P); if (c.pass) ok++; sum += Math.max(-95, c.best);
    const i = k % h.cols, j = Math.floor(k / h.cols);
    rooms.forEach(R => { if (i >= R.i0 && i < R.i1 && j >= R.j0 && j < R.j1){ const o = rc[R.r.id] = rc[R.r.id] || {n:0, ok:0, ap:{}}; o.n++; if (c.pass) o.ok++; if (c.bi >= 0){ const id = h.A[c.bi].a.id; o.ap[id] = (o.ap[id] || 0) + 1; } } }); }
  const roomsOut = {}; for (const id in rc) roomsOut[id] = {pct:Math.round(rc[id].ok / rc[id].n * 100), ap:rc[id].ap, n:rc[id].n};
  return {pct:Math.round(ok / n * 100), rooms:roomsOut, n, avg:Math.round(sum / n)};
}
const loadBand = d => d.aps.some(a => radioOn(a, "5")) ? "5" : d.view.band;
// Client load: users of each room × devices per user, split between the APs that serve the room.
function clientLoad(d){
  const L = {}, b = loadBand(d);
  d.floors.forEach(f => { if (!f.rooms.some(r => num(r.users) > 0)) return; const E = evalFloor(d, f, b);
    f.rooms.forEach(r => { const u = num(r.users) * num(d.cfg.dpu, 1.5), R = E.rooms[r.id]; if (!u || !R) return; const tot = Object.values(R.ap).reduce((x, y) => x + y, 0) || 1;
      for (const id in R.ap) L[id] = (L[id] || 0) + u * R.ap[id] / tot; }); });
  return L;
}
// Cable run from the floor's IDF / rack (orthogonal route + vertical allowance + slack; riser between floors).
function cableLen(d, a){
  if (num(a.cable) > 0) return num(a.cable);
  const dv = devOf(a), l = dv && linksOf(B(), dv.id).find(x => num(x.len) > 0); if (l) return num(l.len);
  const fi = d.floors.findIndex(f => f.id === a.floor); if (fi < 0) return null;
  let best = null;
  d.floors.forEach((f, j) => { if (!f.idf || apart(f.id, a.floor)) return; const k = Math.abs(j - fi), dx = k ? 0 : Math.abs(a.x - f.idf.x) + Math.abs(a.y - f.idf.y), own = d.floors[fi];
    const run = k ? (own.idf ? null : Math.abs(a.x - f.idf.x) + Math.abs(a.y - f.idf.y) + k * d.cfg.floorH) : dx; if (run === null) return;
    const L = run + num(d.cfg.vert, 4) + num(d.cfg.slack, 3); if (best === null || L < best) best = L; });
  return best === null ? null : Math.round(best);
}

/* ---------- automatic channel plan (greedy, interference-weighted) ---------- */
function apPairLoss(d, a, c, b){
  const fa = d.floors.findIndex(f => f.id === a.floor), fc = d.floors.findIndex(f => f.id === c.floor); if (fa < 0 || fc < 0 || apart(a.floor, c.floor)) return -200;
  const k = Math.abs(fa - fc); if (k > 2) return -200;
  const f = d.floors[fc], A = {a, k, dz:k * d.cfg.floorH, eirp:txOf(a, b) + gainOf(a, b)};
  return sigAt(d, b, A, c.x, c.y, k ? [] : wallsOf(f, b));
}
function autoChan(d, bands){
  const done = [];
  bands.forEach(b => {
    const list = d.aps.filter(a => radioOn(a, b)); if (!list.length) return;
    const w = b === "2.4" ? 20 : b === "5" ? num(d.cfg.w5, 40) : num(d.cfg.w6, 80);
    const chs = chList(b, w, d.cfg.dfs); if (!chs.length) return;
    const I = new Map(); list.forEach(a => list.forEach(c => { if (a !== c) I.set(a.id + c.id, Math.pow(10, apPairLoss(d, a, c, b) / 10)); }));
    const deg = a => list.reduce((s, c) => s + (I.get(a.id + c.id) || 0), 0);
    const order = [...list].sort((p, q) => deg(q) - deg(p)), use = {}, asg = new Map();
    order.forEach(a => { let bc = chs[0], bv = Infinity;
      chs.forEach(ch => { const sp = span(b, ch, w); let v = 0; asg.forEach((ch2, id) => { if (overlap(sp, span(b, ch2, w))) v += (I.get(id + a.id) || 0) + (I.get(a.id + id) || 0); }); v += (use[ch] || 0) * 1e-15;
        if (v < bv - 1e-18){ bv = v; bc = ch; } });
      asg.set(a.id, bc); use[bc] = (use[bc] || 0) + 1; });
    list.forEach(a => { a.radios[b].ch = asg.get(a.id); a.radios[b].w = w; });
    done.push(b);
  });
  return done;
}

/* ---------- heatmap drawing ---------- */
function paintHeat(d, f, step, cv, view, b){
  const ctx = cv.getContext("2d"); ctx.clearRect(0, 0, cv.width, cv.height);
  const h = heat(d, f, b, step); if (!h.nA) return h;
  if (!(h.cols > 0 && h.rows > 0 && isFinite(h.cols) && isFinite(h.rows))) return h;   // floor size not a number (yet): nothing to paint
  const P = prof(d), off = document.createElement("canvas"); off.width = h.cols; off.height = h.rows;
  const oc = off.getContext("2d"), img = oc.createImageData(h.cols, h.rows), op = num(d.view.op, 70) / 70;
  for (let k = 0; k < h.cols * h.rows; k++){ const c = colorFor(d, view, cellInfo(d, h, k, b, P), h); if (c){ c[3] = Math.min(255, Math.round(c[3] * op)); img.data.set(c, k * 4); } }
  oc.putImageData(img, 0, 0); ctx.imageSmoothingEnabled = !["best","pass","cnt","cci"].includes(view); ctx.imageSmoothingQuality = "high"; ctx.drawImage(off, 0, 0, cv.width, cv.height);
  return h;
}
function drawHeat(d, f, step){ document.querySelectorAll(`canvas[data-heat="${f.id}"]`).forEach(cv => paintHeat(d, f, step, cv, d.view.mode, d.view.band)); }

/* ---------- small UI helpers ---------- */
const panel = (title, body, btns = "") => `<div class="card wpan"><h3>${esc(title)}<span class="grow"></span>${btns ? `<span class="noprint">${btns}</span>` : ""}</h3>${body}</div>`;
const pill = (txt, cls) => `<span class="pill ${cls || ""}">${esc(txt)}</span>`;
function tableRO(cols, rows){
  return `<div class="scroll"><table class="t"><tr>${cols.map(c => `<th${c.c ? ' class="c"' : ""}>${esc(c.label)}</th>`).join("")}</tr>${rows.map(r => `<tr${r._attr || ""}>${cols.map(c => `<td${c.c ? ' class="c"' : ""}${c.b ? ' style="font-weight:700"' : ""}${c.nw ? ' style="white-space:nowrap"' : ""}>${c.html ? (r[c.k] ?? "") : esc(r[c.k] ?? "")}</td>`).join("")}</tr>`).join("")}</table></div>`;
}
const field = (label, k, v, type = "text", extra = "") => type === "textarea" ? `<label class="fld"><span>${esc(label)}</span><textarea data-f="${k}"${extra}>${esc(v ?? "")}</textarea></label>` : `<label class="fld"><span>${esc(label)}</span><input data-f="${k}" type="${type}" value="${esc(v ?? "")}"${extra}></label>`;
const selField = (label, k, v, opts) => `<label class="fld"><span>${esc(label)}</span><select data-f="${k}">${opts.map(([a, l]) => opt(a, l, v)).join("")}</select></label>`;
const notesBody = list => list.length ? `<ul class="notes">${list.map(n => `<li>${esc(n)}</li>`).join("")}</ul>` : `<div class="muted">—</div>`;
function exportCSV(name, header, rows){ saveText(fileSafe(B().name) + " - " + name + ".csv", csvText(header, rows), "csv", "text/csv"); }

/* ---------- plan rendering ---------- */
function plansHtml(d, print){
  if (!d.floors.length) return `<div class="empty"><h3>${esc(t("wEmptyT"))}</h3><p>${esc(t("wEmpty"))}</p><div class="btns" style="justify-content:center"><button class="btn pri" data-wa="addFloor">＋ ${esc(t("addFloor"))}</button></div></div>`;
  // the site plan is printed only when something is on it
  if (print) return `<div class="plans">${d.floors.filter(f => f.id !== OUT_FLOOR || f.img || f.rooms.length || d.aps.some(a => a.floor === OUT_FLOOR)).map(f => floorRow(d, f, print)).join("")}</div>`;
  // one floor at a time, chosen with the floor tabs (same as Building structure and CCTV)
  const cur = d.floors.find(f => f.id === UI.wfFloor) || d.floors[d.floors.length - 1]; UI.wfFloor = cur.id;
  return `<div class="bfloors">${d.floors.map(f => `<button class="bfchip${f === cur ? " on" : ""}" data-wfl="${f.id}">${f.id === OUT_FLOOR ? "🌳" : "🏬"} ${esc(fName(f))} <small>${d.aps.filter(a => a.floor === f.id && a.status !== "removed").length} AP</small></button>`).join("")}</div><div class="plans">${floorRow(d, cur, print)}</div>`;
}
function legendHtml(d){
  const m = d.view.mode, P = prof(d), sw = (c, l) => `<div><i style="background:${c}"></i>${l}</div>`, rgb = c => `rgb(${c})`;
  let h = "";
  if (m === "rssi" || m === "sec") h = RSTOPS.map(([v, c]) => sw(rgb(c), `${v} dBm`)).join("");
  else if (m === "snr") h = SSTOPS.map(([v, c]) => sw(rgb(c), `${v} dB`)).join("");
  else if (m === "rate") h = RATESTOPS.map(([v, c]) => sw(rgb(c), `${v} Mbps`)).join("");
  else if (m === "cnt") h = [["rgb(42,160,70)","3+"],["rgb(150,205,90)","2"],["rgb(245,205,70)","1"],["rgb(220,80,60)","0"]].map(([c, l]) => sw(c, `${l} AP ≥ ${P.cntR}`)).join("");
  else if (m === "cci") h = [["rgb(42,160,70)","0"],["rgb(245,205,70)","1"],["rgb(245,150,60)","2"],["rgb(215,55,45)","3+"]].map(([c, l]) => sw(c, `${l} CCI`)).join("");
  else if (m === "pass") h = sw("rgb(42,160,70)", esc(t("lg_pass"))) + sw("rgb(215,55,45)", esc(t("lg_fail")));
  else h = d.aps.slice(0, 12).map((a, i) => sw(APCOL[i % APCOL.length], esc(a.name))).join("");
  return `<div class="sigs">${h}</div><div class="muted small" style="margin:8px 0 0">${esc(t("lgx_" + m, {r:P.rssi, s:P.snr, n:d.cfg.nf[d.view.band], c:d.cfg.css}))}</div>`;
}
function floorRow(d, f, print){
  const s = PW / f.wm, H = Math.round(f.hm * s), [bg, fg] = FC[f.color] || FC.blue, E = evalFloor(d, f, d.view.band), P = prof(d), nA = d.aps.filter(a => a.floor === f.id && a.status !== "removed").length;
  const url = f.img ? assetURL(f.img) : "";
  return `<div class="frow"><div class="fcard${!print && S() === f.id ? " on" : ""}" data-fl="${f.id}" style="background:${bg};border-color:${fg}">
    <div class="ft" style="color:${fg}">${lines(f.name).map(esc).join("<br>")}</div><ul>${lines(f.desc).filter(Boolean).map(x => `<li>${esc(x)}</li>`).join("")}</ul>
    <div class="cov">${nA ? `<span class="${E.pct >= P.cover ? "okc" : "badc"}">${esc(t("passS",{p:E.pct}))}</span><br>${esc(t("cardAps",{n:nA, a:Math.round(f.wm * f.hm)}))}` : esc(t("w_noAPs"))}</div></div>
    <div class="planwrap">${print ? "" : `<div class="zp" data-zp="wifi:${f.id}" style="height:min(78vh,${H + 60}px)"><div class="zpi">`}<div class="plan${tool !== "select" && !print ? " tool" : ""}" style="width:${PW}px;height:${H}px">
      ${f.pv && f.pv.vec ? `${url && num(f.pv.bgop, 0) ? `<img src="${url}" alt="" style="opacity:${num(f.pv.bgop, 0) / 100}">` : ""}<svg class="bgv" viewBox="0 0 ${PW} ${H}" width="${PW}" height="${H}" style="position:absolute;left:0;top:0;pointer-events:none">${DRAW.bgSvg(f.pv, s)}</svg>` : url ? `<img src="${url}" alt="" style="opacity:${num(f.op, 60) / 100}">` : ""}
      <canvas class="heat" data-heat="${f.id}" width="${PW}" height="${H}"></canvas>
      <svg class="over" ${print ? "" : `data-ov="${f.id}"`} viewBox="0 0 ${PW} ${H}" width="${PW}" height="${H}">${overSvg(d, f, print)}</svg>
      <div class="scalebar">${scaleBar(f)}</div>
    </div>${print ? "" : `</div><div class="zpbtn"><button data-zpa="in">＋</button><button data-zpa="out">－</button><button data-zpa="fit" title="${esc(t("zpFit"))}">⤢</button><span class="zpz"></span></div><div class="zphint">${esc(t("zpHint"))}</div></div>`}</div></div>`;
}
function scaleBar(f){ const s = PW / f.wm, m = [1,2,5,10,20,50].find(v => v * s >= 60) || 50; return `<i style="width:${m * s}px"></i>${m} m`; }
function overSvg(d, f, print){
  const s = PW / f.wm, H = Math.round(f.hm * s), b = d.view.band, sel = print ? null : S();
  let h = `<rect class="bgp" x="0" y="0" width="${PW}" height="${H}" fill="transparent"/>`;
  f.rooms.forEach(r => {
    const x = r.x * s, y = r.y * s, w = r.w * s, hh = r.h * s, ls = lines(r.label);
    if (Array.isArray(r.poly) && r.poly.length >= 6){ // room from a drawing: its real outline (thin), its name where the drawing has it
      const sx = r.pw ? r.w / r.pw : 1, sy = r.ph ? r.h / r.ph : 1, pts = []; for (let i = 0; i + 1 < r.poly.length; i += 2) pts.push(((r.x + r.poly[i] * sx) * s).toFixed(1) + "," + ((r.y + r.poly[i + 1] * sy) * s).toFixed(1));
      const lx = (r.x + (r.lx !== undefined ? r.lx * sx : r.w / 2)) * s, ly = (r.y + (r.ly !== undefined ? r.ly * sy : r.h / 2)) * s;
      h += `<g class="rm" data-room="${r.id}"><polygon points="${pts.join(" ")}" fill="rgba(255,255,255,.01)" stroke="#8a93a8" stroke-width=".8" stroke-dasharray="4 3"/>
        <text class="rlab" data-rlab="${r.id}" x="${lx}" y="${ly}" font-size="${clamp(s * .32, 7.5, 11)}" font-weight="700" text-anchor="middle" fill="#20242e" stroke="#fff" stroke-width="2.4" paint-order="stroke">${esc(ls.join(" "))}</text></g>`;
      if (sel === r.id) h += `<rect class="rsel" x="${x - 3}" y="${y - 3}" width="${w + 6}" height="${hh + 6}"/>`;
      return; }
    h += `<g class="rm" data-room="${r.id}"><rect x="${x}" y="${y}" width="${w}" height="${hh}" fill="rgba(255,255,255,.01)" ${MSTYLE[r.wall] || MSTYLE.drywall}/>
      <text class="rlab" data-rlab="${r.id}" x="${r.lx !== undefined ? (r.x + r.lx) * s : x + w/2}" y="${r.ly !== undefined ? (r.y + r.ly) * s : y + hh/2 - (ls.length - 1) * 6 + 4}" font-size="${ls.length > 1 || w < 70 ? 9.5 : 11}" font-weight="700" text-anchor="middle" fill="#20242e" stroke="#fff" stroke-width="2.4" paint-order="stroke">${ls.map((l, i) => `<tspan x="${r.lx !== undefined ? (r.x + r.lx) * s : x + w/2}" dy="${i ? 12 : 0}">${esc(l)}</tspan>`).join("")}</text>
      ${num(r.users) ? `<text x="${x + w - 4}" y="${y + 11}" font-size="8.5" text-anchor="end" fill="#3b4256">👤${num(r.users)}</text>` : ""}</g>`;
    if (sel === r.id) h += `<rect class="rsel" x="${x - 3}" y="${y - 3}" width="${w + 6}" height="${hh + 6}"/><rect class="rh" data-rh="${r.id}" x="${x + w - 6}" y="${y + hh - 6}" width="12" height="12" rx="2"/>`;
  });
  f.walls.forEach(w => { const st = MSTYLE[w.mat] || MSTYLE.drywall;
    const wd = DRAW.wallD(w, s);
    h += `<g data-wall="${w.id}" class="wl"><path d="${wd}" fill="none" stroke="transparent" stroke-width="12"/><path d="${wd}" fill="none" ${st} stroke-linecap="round"/>
      ${w.kind === "door" ? `<circle cx="${(w.x1 + w.x2) / 2 * s}" cy="${(w.y1 + w.y2) / 2 * s}" r="3" fill="#b0702a"/>` : w.kind === "window" ? `<line x1="${w.x1 * s}" y1="${w.y1 * s}" x2="${w.x2 * s}" y2="${w.y2 * s}" stroke="#fff" stroke-width="1"/>` : ""}</g>`;
    if (sel === w.id) h += `<path d="${DRAW.wallD(w, s)}" fill="none" stroke="#ffb703" stroke-width="7" opacity=".45" pointer-events="none"/><circle class="wh" data-wh="${w.id}:1" cx="${w.x1 * s}" cy="${w.y1 * s}" r="6"/><circle class="wh" data-wh="${w.id}:2" cx="${w.x2 * s}" cy="${w.y2 * s}" r="6"/>`; });
  if (f.idf){ const x = f.idf.x * s, y = f.idf.y * s;
    if (d.view.cable) d.aps.filter(a => a.floor === f.id && a.status !== "removed").forEach(a => { h += `<path d="M${x} ${y}H${a.x * s}V${a.y * s}" fill="none" stroke="#8a6d1f" stroke-width="1.2" stroke-dasharray="4 3" opacity=".8"/>`; });
    h += `<g class="idf" data-idf="${f.id}" transform="translate(${x} ${y})"><rect x="-11" y="-13" width="22" height="26" rx="3" fill="#1d2433" stroke="#fff" stroke-width="1.5"/><path d="M-6 -7h12M-6 -2h12M-6 3h12M-6 8h12" stroke="#7fd1ff" stroke-width="2"/><text y="24" font-size="9" font-weight="700" text-anchor="middle" fill="#1d2433" stroke="#fff" stroke-width="2.5" paint-order="stroke">IDF</text></g>`; }
  if (d.view.survey) f.survey.filter(p => p.band === b).forEach(p => { const pr = predictAt(d, f, b, p.x, p.y), dl = pr === null ? null : Math.round(num(p.rssi) - pr), on = sel === p.id;
    h += `<g class="svp" data-sv="${p.id}" transform="translate(${p.x * s} ${p.y * s})"><path d="M0 -9L8 5H-8Z" fill="${dl !== null && Math.abs(dl) > 8 ? "#d63a3a" : "#16a3a3"}" stroke="${on ? "#ffb703" : "#fff"}" stroke-width="${on ? 3 : 1.4}"/>
      <text y="17" font-size="9" font-weight="700" text-anchor="middle" fill="#0d3b3b" stroke="#fff" stroke-width="2.5" paint-order="stroke">${num(p.rssi)}${dl !== null ? ` (${dl > 0 ? "+" : ""}${dl})` : ""}</text></g>`; });
  d.aps.filter(a => a.floor === f.id).forEach(a => {
    const x = a.x * s, y = a.y * s, on = sel === a.id, q = d.aps.indexOf(a), r = radio(a, b), stc = a.status === "faulty" ? "#d63a3a" : a.status === "removed" ? "#9aa3b5" : a.status === "planned" ? "#9fb3d8" : "#2a9d3a";
    const chs = d.view.chan && radioOn(a, b) ? `ch ${r.ch}${b !== "2.4" ? "/" + r.w : ""} · ${txOf(a, b)} dBm` : (radioOn(a, b) ? "" : `${b} GHz off`);
    h += `<g class="apm" data-ap="${a.id}" transform="translate(${x} ${y})"${a.status === "removed" ? ' opacity=".45"' : ""}>
      ${on ? `<circle r="22" fill="none" stroke="#ffb703" stroke-width="3"/>` : ""}
      ${d.view.mode === "best" ? `<circle r="20" fill="${APCOL[q % APCOL.length]}" opacity=".9"/>` : ""}
      <circle r="17" fill="#fff" stroke="${stc}" stroke-width="${a.status === "planned" ? 1.6 : 2.4}"${a.status === "planned" ? ' stroke-dasharray="3 2"' : ""}/>
      <path d="M-9 -2a13 13 0 0 1 18 0M-5.5 2a8 8 0 0 1 11 0" fill="none" stroke="#1e6fd9" stroke-width="2.4" stroke-linecap="round"/><circle cx="0" cy="6" r="2.2" fill="#1e6fd9"/>
      <text y="30" font-size="9.5" font-weight="700" text-anchor="middle" fill="#1d2433" stroke="#fff" stroke-width="3" paint-order="stroke">${esc(a.name)}</text>
      ${chs ? `<text y="40" font-size="8.2" text-anchor="middle" fill="#1f4fbf" stroke="#fff" stroke-width="2.6" paint-order="stroke">${esc(chs)}</text>` : ""}</g>`;
  });
  if (!print && pend && pend.f === f.id) h += `<circle cx="${pend.x * s}" cy="${pend.y * s}" r="4" fill="#ffb703" stroke="#1d2433"/><line class="wprev" x1="${pend.x * s}" y1="${pend.y * s}" x2="${pend.x * s}" y2="${pend.y * s}" stroke="#ffb703" stroke-width="2.5" stroke-dasharray="5 3"/><text class="wlen" font-size="10" font-weight="700" fill="#1d2433" stroke="#fff" stroke-width="3" paint-order="stroke"></text>`;
  if (!print && mline && mline.f === f.id) h += `<line x1="${mline.x1 * s}" y1="${mline.y1 * s}" x2="${mline.x2 * s}" y2="${mline.y2 * s}" stroke="#d0453b" stroke-width="2"/><text x="${(mline.x1 + mline.x2) / 2 * s + 6}" y="${(mline.y1 + mline.y2) / 2 * s - 6}" font-size="11" font-weight="800" fill="#d0453b" stroke="#fff" stroke-width="3" paint-order="stroke">${r1(Math.hypot(mline.x2 - mline.x1, mline.y2 - mline.y1))} m</text>`;
  return h;
}
function predictAt(d, f, b, x, y){ const A = apsFor(d, f, b); if (!A.length) return null; const W = wallsOf(f, b); return Math.max(...A.map(q => sigAt(d, b, q, x, y, W))); }
function roomAt(d, a){ const f = d.floors.find(x => x.id === a.floor); if (!f) return null; const In = r => a.x >= r.x && a.x <= r.x + r.w && a.y >= r.y && a.y <= r.y + r.h; return f.rooms.filter(r => r.wall !== "none" && In(r))[0] || f.rooms.find(In); }

/* ---------- tables ---------- */
function apTable(d){
  const rows = [...d.aps].sort((a, b) => String(a.name).localeCompare(String(b.name), undefined, {numeric:true}));
  if (!rows.length) return `<p class="muted">${esc(t("noPlacedAps"))}</p>`;
  const used = BANDS.filter(b => d.aps.some(a => radioOn(a, b))), CL = clientLoad(d), sel = S();
  return `<div class="scroll"><table class="t apt"><tr><th>AP</th><th>${esc(t("f_floor"))}</th><th>${esc(t("f_model"))}</th>${used.map(b => `<th>${b} GHz<br><span class="muted">ch / MHz / dBm</span></th>`).join("")}<th>Switch :port / VLAN</th><th>${esc(t("c_cable"))}</th><th>${esc(t("c_cl"))}</th></tr>${rows.map(a => {
    const f = d.floors.find(x => x.id === a.floor), rm = roomAt(d, a), L = cableLen(d, a), cl = Math.round(CL[a.id] || 0);
    return `<tr class="click${sel === a.id ? " on" : ""}" data-sel="dev:${a.id}"><td><b>${esc(a.name)}</b>${a.status !== "active" ? `<br><span class="muted">${esc(gt("st_" + a.status))}</span>` : ""}</td><td>${esc(fShort(f))}${rm ? `<br><span class="muted">(${esc(rLabel(rm))})</span>` : ""}</td><td>${esc(a.model || "—")}<br><span class="muted">${a.mount === "wall" ? esc(t("m_wall")) : esc(t("m_ceil"))} ${num(a.h)} m</span></td>
      ${used.map(b => { const r = radio(a, b); return `<td class="c">${radioOn(a, b) ? `${r.ch}${b !== "2.4" ? " / " + r.w : ""}<br><span class="muted">${txOf(a, b)} dBm</span>${b === "5" && isDFS(num(r.ch)) ? ' <span class="pill">DFS</span>' : ""}` : "—"}</td>`; }).join("")}
      <td>${esc(a.sw ? a.sw + " :" + a.port : "—")}<br>VLAN: ${esc(a.vlans || "—")}</td><td class="c ${L !== null && L > 90 ? "badc" : ""}">${L === null ? "—" : L + " m"}</td><td class="c ${cl > d.cfg.cpa ? "badc" : ""}">${cl || "—"}</td></tr>`; }).join("")}</table></div>`;
}
function resultsPanel(d){
  if (!d.floors.length) return "";
  const b = d.view.band, P = prof(d);
  const fr = d.floors.map(f => { const E = evalFloor(d, f, b), n = d.aps.filter(a => a.floor === f.id && a.status !== "removed").length;
    return {_attr:` class="click" data-wgo="${f.id}"`, f:fShort(f), ap:n, area:Math.round(f.wm * f.hm) + " m²", avg:E.avg === null ? "—" : E.avg + " dBm", pct:n ? pill(E.pct + "%", E.pct >= P.cover ? "ok" : "bad") : "—"}; });
  const RR = []; d.floors.forEach(f => { const E = evalFloor(d, f, b); f.rooms.forEach(r => { const q = E.rooms[r.id]; if (!num(r.users) && !(q && q.pct < P.cover)) return; RR.push({_attr:` class="click" data-wgo="${r.id}"`, r:rLabel(r), f:fShort(f), u:num(r.users) || "", m:t("mat_" + r.wall), pct:q ? pill(q.pct + "%", q.pct >= P.cover ? "ok" : "bad") : "—"}); }); });
  const T1 = tableRO([{k:"f", label:t("c_floorS"), b:1}, {k:"ap", label:"AP", c:1}, {k:"area", label:t("c_area"), c:1}, {k:"avg", label:t("c_avg"), c:1}, {k:"pct", label:t("c_pass",{p:P.cover}), c:1, html:1}], fr);
  const T2 = RR.length ? tableRO([{k:"r", label:t("c_room"), b:1}, {k:"f", label:t("c_floorS")}, {k:"m", label:t("c_mat")}, {k:"u", label:t("c_users"), c:1}, {k:"pct", label:t("c_pass",{p:P.cover}), c:1, html:1}], RR) : "";
  return panel(t("resHdr",{p:t("pr_" + d.cfg.prof), f:b}), `<div class="muted small" style="margin-bottom:6px">${esc(t("resHint",{r:P.rssi, s:P.snr, sec:P.sec === "" ? "—" : P.sec, c:P.cnt, cr:P.cntR, i:P.cci}))}</div>` + T1 + (T2 ? `<div style="height:8px"></div>` + T2 : ""), `<button class="btn small" data-wcsv="rooms">⤓ CSV</button>`);
}
// PoE drawn by the APs on each switch (from the cables in the building) against the switch's PoE budget / ports.
function swLoad(d){ const S2 = {}; d.aps.filter(a => a.status !== "removed" && a.swId).forEach(a => { const o = S2[a.swId] = S2[a.swId] || {n:0, w:0}; o.n++; o.w += MOD(a).poe; }); return S2; }
function swPanel(d){
  const S2 = swLoad(d), b = B(), rows = Object.keys(S2).map(id => { const sw = devById(b, id), o = S2[id], bud = num(sw && sw.params.poeBudget), pts = num(sw && (sw.params.poePorts || sw.ports));
    return {_attr:` class="click" data-sel="dev:${id}"`, n:devLabel(sw), c:`${o.n}${pts ? " / " + pts : ""}`, w:`${r1(o.w)}${bud ? " / " + bud : ""} W`, st:(bud && o.w > bud) || (pts && o.n > pts) ? pill(t("short"), "bad") : bud ? pill(Math.round(o.w / bud * 100) + "%", o.w > .8 * bud ? "warn" : "ok") : "—"}; });
  return panel(t("swHdr"), rows.length ? tableRO([{k:"n", label:"Switch", b:1}, {k:"c", label:t("c_apPorts"), c:1}, {k:"w", label:"PoE", c:1}, {k:"st", label:"", c:1, html:1}], rows) : `<p class="muted small">${esc(t("swNone"))}</p>`);
}
function bomRows(d){
  const M = {}; d.aps.filter(a => a.status !== "removed").forEach(a => { const m = MOD(a), k = a.model || "—"; M[k] = M[k] || {item:k, spec:[m.std, m.poe ? `PoE ${m.poe} W` : "", m.cls].filter(Boolean).join(", "), qty:0}; M[k].qty++; });
  const R = Object.values(M), n = R.reduce((s, r) => s + r.qty, 0), cab = d.aps.filter(a => a.status !== "removed").reduce((s, a) => s + (cableLen(d, a) || 0), 0);
  if (n){ R.push({item:t("bom_mount"), spec:t("bom_mountS"), qty:n}); R.push({item:t("bom_cable"), spec:t("bom_cableS"), qty:`${Math.ceil(cab * 1.1)} m`}); R.push({item:t("bom_jack"), spec:"RJ45 Cat6A", qty:n * 2}); R.push({item:t("bom_patch"), spec:"Cat6A, 1–3 m", qty:n * 2}); }
  return R;
}
function bomPanel(d){ const R = bomRows(d); return R.length ? panel(t("bomHdr"), tableRO([{k:"item", label:t("c_item"), b:1}, {k:"spec", label:t("c_spec")}, {k:"qty", label:t("c_qty"), c:1, nw:1}], R), `<button class="btn small" data-wcsv="bom">⤓ CSV</button>`) : ""; }
function surveyRows(d){ const R = []; d.floors.forEach(f => f.survey.forEach((p, i) => { const pr = predictAt(d, f, p.band, p.x, p.y); R.push({_attr:` class="click" data-wgo="${p.id}"`, f:fShort(f), n:p.name || "P" + (i + 1), band:p.band + " GHz", m:num(p.rssi), p:pr === null ? "—" : Math.round(pr), dl:pr === null ? "—" : Math.round(num(p.rssi) - pr), note:p.note || ""}); })); return R; }
function surveyPanel(d){
  const R = surveyRows(d); if (!R.length) return "";
  const dl = R.filter(r => r.dl !== "—").map(r => r.dl), me = dl.length ? r1(dl.reduce((a, b) => a + b, 0) / dl.length) : 0, mae = dl.length ? r1(dl.reduce((a, b) => a + Math.abs(b), 0) / dl.length) : 0;
  return panel(t("svHdr"), tableRO([{k:"n", label:"#", b:1}, {k:"f", label:t("c_floorS")}, {k:"band", label:"Band", c:1, nw:1}, {k:"m", label:t("c_meas"), c:1}, {k:"p", label:t("c_pred"), c:1}, {k:"dl", label:"Δ dB", c:1}, {k:"note", label:t("c_note")}], R)
    + `<div class="muted small" style="margin-top:6px">${esc(t("svHint",{me, mae}))}</div>`, `<button class="btn small" data-wcsv="survey">⤓ CSV</button>`);
}
function ssidTable(d){
  const R = d.tables.ssid, cols = [["ssid", t("c_ssid"), "150px"], ["purpose", t("c_purpose"), "140px"], ["vlan", "VLAN", "60px"], ["band", t("c_bandS"), "90px"], ["sec", t("c_sec"), "200px"]];
  return `<div class="scroll"><table class="t"><tr>${cols.map(c => `<th>${esc(c[1])}</th>`).join("")}<th></th></tr>${R.map((r, i) => `<tr>${cols.map(([k, , w]) => `<td><input data-wt="${i}:${k}" value="${esc(r[k] ?? "")}" style="min-width:${w}"></td>`).join("")}<td><button class="btn small dan" data-wa="ssidDel" data-r="${i}" title="${esc(t("delete"))}">×</button></td></tr>`).join("")}</table></div><button class="btn small" data-wa="ssidAdd">＋ ${esc(t("addRow"))}</button>`;
}
function overview(d){
  const F = d.floors.slice().reverse(), n = F.length || 1, gap = 64, H = n * gap + 66;
  const iso = (u, v, lv) => [14 + u * 160 + v * 52, H - 46 - lv * gap + v * 34 - u * 24];
  let g = "";
  F.forEach((f, lv) => {
    const pts = [[0,0],[1,0],[1,1],[0,1]].map(([u, v]) => iso(u, v, lv).join(",")).join(" ");
    g += `<polygon points="${pts}" fill="#eef0f4" stroke="#8a93a6" stroke-width="1.2"/>`;
    f.rooms.filter(r => r.wall !== "none").forEach(r => { const P = [[r.x, r.y], [r.x + r.w, r.y], [r.x + r.w, r.y + r.h], [r.x, r.y + r.h]].map(([x, y]) => iso(x / f.wm, y / f.hm, lv).join(",")).join(" "); g += `<polygon points="${P}" fill="none" stroke="#b5bccb" stroke-width=".7"/>`; });
    d.aps.filter(a => a.floor === f.id && a.status !== "removed").forEach(a => { const [x, y] = iso(a.x / f.wm, a.y / f.hm, lv); g += `<g transform="translate(${x} ${y - 6})"><path d="M-6 0a8 8 0 0 1 12 0M-3.5 3a4.5 4.5 0 0 1 7 0" fill="none" stroke="#1f9d55" stroke-width="2" stroke-linecap="round"/><circle cy="6" r="1.6" fill="#1f9d55"/></g>`; });
    if (f.idf){ const [x, y] = iso(f.idf.x / f.wm, f.idf.y / f.hm, lv); g += `<rect x="${x - 3}" y="${y - 8}" width="6" height="8" fill="#1d2433"/>`; }
    const [lx, ly] = iso(1, .5, lv), names = d.aps.filter(a => a.floor === f.id && a.status !== "removed").map(a => a.name).join(", ");
    g += `<text x="${lx + 14}" y="${ly - 8}" font-size="10.5" font-weight="700" fill="#1d2433">${esc(fShort(f))}</text><text x="${lx + 14}" y="${ly + 6}" font-size="10" fill="#1f5fbf">${esc(names ? "(" + names + ")" : "")}</text>`;
  });
  if (F.length > 1){ const [x1, y1] = iso(.08, .5, 0), [x2, y2] = iso(.08, .5, F.length - 1); g += `<path d="M${x1} ${y1}L${x2} ${y2}" stroke="#1e6fd9" stroke-width="1.6" stroke-dasharray="5 4"/>`; }
  return `<svg class="ovsvg" viewBox="0 0 370 ${H}" width="100%" style="max-width:420px;background:#fff;border-radius:6px">${g}</svg>`;
}

/* ---------- palette (tools & view) ---------- */
let lastMat = {wall:"drywall", door:"door", window:"glass"};
const curMat = () => lastMat[tool] || "drywall";
function unplacedAps(){ const b = B(), fids = new Set(b.floors.map(f => f.id)); return b.devices.filter(x => x.kind === "ap" && !(x.ap.x !== null && x.ap.x !== undefined && x.ap.x !== "" && fids.has(x.floor))); }
function wifiPalette(){
  const d = D(), v = d.view, T = (k, ic, key) => `<div class="wtool${tool === k ? " on" : ""}" data-tool="${k}" title="${esc(t("tl_" + k))}${key ? " (" + key + ")" : ""}"><b>${ic}</b><span>${esc(t("tl_" + k))}</span></div>`;
  const o = (arr, cur, lab) => arr.map(x => opt(x, lab(x), String(cur))).join("");
  const U = unplacedAps();
  return `${U.length ? `<div class="psec"><h4>${esc(t("unplacedAps"))} <span class="cnt">${U.length}</span></h4><div class="ulist">${U.slice(0, 40).map(x => `<button class="ub${placeId === x.id ? " on" : ""}" data-wplace="${x.id}" title="${esc(t("placeHint"))}">📶 ${esc(devLabel(x))}</button>`).join("")}</div></div>` : ""}
  <div class="psec"><h4>${esc(t("palTools"))}</h4><div class="wtools">${T("select","↖","V")}${T("room","▭","R")}${T("wall","▬","W")}${T("door","🚪","D")}${T("window","🪟","N")}${T("ap","📶","A")}${T("survey","📍","S")}${T("idf","🗄","")}${T("calib","📏","")}${T("measure","📐","M")}</div>
  ${placeId ? `<p class="toolhint">${esc(t("placeHint"))}</p>` : tool !== "select" ? `<p class="toolhint">${esc(t("th_" + tool))}</p>` : ""}
  ${["wall","door","window"].includes(tool) ? `<label class="fld"><span>${esc(t("f_mat"))}</span><select data-wv="mat">${o(Object.keys(MAT), curMat(), m => `${t("mat_" + m)} (${MAT[m].join("/")})`)}</select></label>` : ""}</div>
  <div class="psec"><h4>${esc(t("palView"))}</h4>
  <label class="fld"><span>${esc(t("f_band"))}</span><select data-wv="band">${o(BANDS, v.band, b => b + " GHz")}</select></label>
  <label class="fld"><span>${esc(t("f_view"))}</span><select data-wv="mode">${o(VIEWS, v.mode, m => t("v_" + m))}</select></label>
  <label class="fld"><span>${esc(t("f_prof"))}</span><select data-wv="prof">${o([...Object.keys(PROF), "custom"], d.cfg.prof, p => t("pr_" + p))}</select></label>
  <label class="fld"><span>${esc(t("f_op"))} ${num(v.op)}%</span><input type="range" min="10" max="100" step="5" value="${num(v.op)}" data-wv="op"></label>
  <label class="chk"><input type="checkbox" data-wv="chan"${v.chan ? " checked" : ""}> ${esc(t("v_chan"))}</label>
  <label class="chk"><input type="checkbox" data-wv="cable"${v.cable ? " checked" : ""}> ${esc(t("v_cable"))}</label>
  <label class="chk"><input type="checkbox" data-wv="survey"${v.survey ? " checked" : ""}> ${esc(t("v_survey"))}</label>
  <button class="btn small wfull" data-wa="autoChan">📡 ${esc(t("autoChan"))}</button>
  <button class="btn small wfull" data-tab="set">🎯 ${esc(t("reqEdit"))}</button></div>
  <div class="psec"><h4>${esc(t("lgHdr",{v:t("v_" + v.mode), f:v.band}))}</h4>${legendHtml(d)}</div>`;
}

/* ---------- drawer ---------- */
const matOpts = () => Object.keys(MAT).map(m => [m, `${t("mat_" + m)} (${MAT[m].join(" / ")} dB)`]);
function wifiDrawer(){
  const d = D(), b = B(), s0 = UI.sel; if (!s0) return "";
  if (s0.type === "dev"){ const dv = devById(b, s0.id); return dv ? deviceEditor(b, dv, {extra:apExtra}) : ""; }
  if (s0.type === "link"){ const l = linkById(b, s0.id); return l ? linkEditor(b, l) : ""; }
  const s = find(d, s0.id); if (!s) return "";
  const head = (title, sub) => `<div class="dhead"><div><h3>${esc(title)}</h3><div class="muted small">${esc(sub)}</div></div><button class="x" data-dr="close">×</button></div>`;
  if (s.kind === "floor"){ const f = s.o;
    return `${head(t("fl"), fName(f))}
    ${field(t("f_ftitle"), "f.name", f.name)}${field(t("f_fdesc"), "f.desc", f.desc, "textarea", ' rows="4"')}
    ${selField(t("f_fcolor"), "f.color", f.color, Object.keys(FC).map(c => [c, t("c_" + c)]))}
    <div class="two">${field(t("f_wm"), "f.wm", f.wm, "number", ' step="0.1"')}${field(t("f_hm"), "f.hm", f.hm, "number", ' step="0.1"')}</div>
    <label class="fld"><span>${esc(t("f_img"))}</span></label><div class="btns" style="margin-top:-4px"><button class="btn" data-dr="loadImg">🖼 ${esc(t("loadImg"))}</button>${f.img ? `<button class="btn dan" data-dr="rmImg">${esc(t("rmImg"))}</button>` : ""}</div>
    ${f.img ? `<div class="muted small" style="margin:-2px 0 6px">${(assetSize(f.img) / 1048576).toFixed(1)} MB</div>${field(t("f_opac"), "f.op", f.op, "number", ' min="0" max="100"')}` : ""}
    <div class="btns"><button class="btn" data-tool="calib">📏 ${esc(t("tl_calib"))}</button><button class="btn" data-tool="idf">🗄 ${esc(f.idf ? t("idfMove") : t("tl_idf"))}</button>${f.idf ? `<button class="btn dan" data-dr="rmIdf">× IDF</button>` : ""}</div>
    <div class="btns"><button class="btn" data-tool="room">▭ ${esc(t("addRoom"))}</button><button class="btn" data-tool="ap">📶 ${esc(t("addAP"))}</button></div>
    ${f.id === OUT_FLOOR ? `<p class="muted small">${esc(t("sitePlanH"))}</p>` : `<div class="btns"><button class="btn" data-dr="floorUp">${esc(t("up"))}</button><button class="btn" data-dr="floorDown">${esc(t("down"))}</button><button class="btn dan" data-dr="delSel">🗑 ${esc(t("delete"))}</button></div>`}`; }
  if (s.kind === "room"){ const r = s.o;
    return `${head(t("room"), fName(s.f) + " · " + r1(r.w * r.h) + " m²")}
    ${field(t("f_label"), "r.label", r.label)}
    ${selField(t("f_wall"), "r.wall", r.wall || "drywall", [["none", t("w_none")], ...matOpts().filter(m => m[0] !== "none")])}
    ${field(t("f_users"), "r.users", r.users ?? 0, "number", ' min="0"')}
    <div class="two">${field(t("f_xm"), "r.x", r.x, "number", ' step="0.1"')}${field(t("f_ym"), "r.y", r.y, "number", ' step="0.1"')}</div>
    <div class="two">${field(t("f_wm"), "r.w", r.w, "number", ' step="0.1"')}${field(t("f_hm"), "r.h", r.h, "number", ' step="0.1"')}</div>
    <div class="btns"><button class="btn" data-dr="dupSel">⧉ ${esc(t("duplicate"))}</button><button class="btn dan" data-dr="delSel">🗑 ${esc(t("delete"))}</button></div><div class="muted small">${esc(t("keys"))}</div>`; }
  if (s.kind === "wall"){ const w = s.o;
    return `${head(t("wallT"), fName(s.f) + " · " + r1(Math.hypot(w.x2 - w.x1, w.y2 - w.y1)) + " m")}
    ${selField(t("f_kind"), "w.kind", w.kind, [["wall", t("tl_wall")], ["door", t("tl_door")], ["window", t("tl_window")]])}
    ${selField(t("f_mat"), "w.mat", w.mat, matOpts())}
    <div class="two">${field("X1 (m)", "w.x1", w.x1, "number", ' step="0.1"')}${field("Y1 (m)", "w.y1", w.y1, "number", ' step="0.1"')}</div>
    <div class="two">${field("X2 (m)", "w.x2", w.x2, "number", ' step="0.1"')}${field("Y2 (m)", "w.y2", w.y2, "number", ' step="0.1"')}</div>
    <div class="btns"><button class="btn" data-dr="dupSel">⧉ ${esc(t("duplicate"))}</button><button class="btn dan" data-dr="delSel">🗑 ${esc(t("delete"))}</button></div><div class="muted small">${esc(t("keys"))}</div>`; }
  if (s.kind === "survey"){ const p = s.o, pr = predictAt(d, s.f, p.band, p.x, p.y);
    return `${head(t("svT"), fName(s.f))}
    ${field(t("f_svname"), "s.name", p.name || "")}${selField(t("f_band"), "s.band", p.band, BANDS.map(x => [x, x + " GHz"]))}
    <div class="two">${field(t("f_svrssi"), "s.rssi", p.rssi, "number")}${field("AP", "s.ap", p.ap || "")}</div>
    <div class="lbox ${pr !== null && Math.abs(num(p.rssi) - pr) > 8 ? "bad" : "ok"}">${esc(t("c_pred"))}: <b>${pr === null ? "—" : Math.round(pr) + " dBm"}</b> · Δ ${pr === null ? "—" : Math.round(num(p.rssi) - pr) + " dB"}</div>
    <div class="two">${field(t("f_xm"), "s.x", p.x, "number", ' step="0.1"')}${field(t("f_ym"), "s.y", p.y, "number", ' step="0.1"')}</div>
    ${field(t("f_note"), "s.note", p.note || "")}<div class="btns"><button class="btn dan" data-dr="delSel">🗑 ${esc(t("delete"))}</button></div>`; }
  return "";
}
// Extra section of the shared device editor for access points: position on the plan, radios, cable and client load.
function apExtra(b, dv){
  if (dv.kind !== "ap") return "";
  const d = D(), a = d.aps.find(x => x.id === dv.id), R = dv.ap.radios;
  const rad = BANDS.map(bd => { const r = R[bd]; if (r.none) return `<tr><td><b>${bd}</b></td><td colspan="4" class="muted">${esc(t("noBand"))}</td></tr>`;
    const w = bd === "2.4" ? [20, 40] : [20, 40, 80, 160], chs = bd === "2.4" ? [...Array(13)].map((_, i) => i + 1) : bd === "5" ? [...CH5N, ...CH5D].sort((x, y) => x - y) : chList("6", 20, true);
    return `<tr><td><label class="chk" style="margin:0"><input type="checkbox" data-wr="${bd}:on"${r.on ? " checked" : ""}> <b>${bd}</b></label></td>
      <td><select data-wr="${bd}:ch">${chs.map(c => opt(c, c, num(r.ch))).join("")}</select></td>
      <td><select data-wr="${bd}:w">${w.map(c => opt(c, c, num(r.w))).join("")}</select></td>
      <td><input type="number" data-wr="${bd}:tx" value="${esc(r.tx)}" min="1" max="${num(r.maxTx, 30)}" style="width:58px"></td><td class="muted small nw">≤${num(r.maxTx)} dBm / ${num(r.gain)} dBi</td></tr>`; }).join("");
  const pos = a ? `<div class="two">${fld(t("f_xm"), "ap.x", a.x, "number", ' step="0.1"')}${fld(t("f_ym"), "ap.y", a.y, "number", ' step="0.1"')}</div>` : `<div class="lbox bad">${esc(t("apNotPlaced"))}</div><button class="btn small" data-dr="placeAp">📍 ${esc(t("placeOnPlan"))}</button>`;
  const L = a ? cableLen(d, a) : null, cl = a ? Math.round(clientLoad(d)[a.id] || 0) : 0;
  return sec("wifi", "📶 " + t("radioSec"), `${pos}
    <div class="two">${sel(t("f_mount"), "ap.mount", dv.ap.mount, opt("ceiling", t("m_ceil"), dv.ap.mount) + opt("wall", t("m_wall"), dv.ap.mount))}${fld(t("f_h"), "ap.h", dv.ap.h, "number", ' step="0.1" min="0.5"')}</div>
    <div class="scroll"><table class="t rtab"><tr><th>Band</th><th>${esc(t("c_ch"))}</th><th>MHz</th><th>Tx dBm</th><th></th></tr>${rad}</table></div>
    <div class="muted small" style="margin:4px 0">${esc([dv.ap.std, dv.params.poeIn ? "PoE " + dv.params.poeIn + " W" : "", dv.ap.maxClients ? t("maxCl") + " " + dv.ap.maxClients : ""].filter(Boolean).join(" · ") || t("apNoModel"))}</div>
    <div class="two">${fld(t("f_vlans"), "ap.vlans", dv.ap.vlans || "", "text", ` placeholder="${esc(portVlans(b, dv) ? "auto: " + portVlans(b, dv) : "10,60,70")}"`)}${fld(t("f_cable"), "ap.cable", dv.ap.cable || "", "number", ` min="0" placeholder="${L === null ? t("noIdf") : "auto " + L}"`)}</div>
    ${a ? `<div class="lbox ${L !== null && L > 90 ? "bad" : "ok"}">${esc(t("c_cable"))}: <b>${L === null ? "—" : L + " m"}</b>${L !== null && L > 90 ? " > 90 m (TIA-568)" : ""} · ${esc(t("c_cl"))}: <b>${cl}</b> / ${d.cfg.cpa}</div>` : ""}`, true);
}
function wifiField(k, raw){
  const d = D(), s = find(d, S()); if (!s) return;
  const [, f] = k.split("."), o = s.o;
  const NUM = new Set(["x","y","w","h","wm","hm","op","x1","y1","x2","y2","users","rssi"]);
  commit(() => {
    let v = NUM.has(f) ? num(raw, o[f]) : raw;
    if (s.kind !== "wall" && (f === "w" || f === "h" || f === "wm" || f === "hm")) v = Math.max(.5, v);
    o[f] = v;
  });
}
function clampAP(d, a){ const f = d.floors.find(x => x.id === a.floor); if (!f) return; a.x = r1(Math.min(f.wm, Math.max(0, a.x))); a.y = r1(Math.min(f.hm, Math.max(0, a.y))); }
function nextAPName(d){ const used = new Set([...B().devices.map(x => x.name), ...d.aps.map(a => a.name)]); let i = 1; while (used.has("AP-" + String(i).padStart(2, "0"))) i++; return "AP-" + String(i).padStart(2, "0"); }
function newAP(d, f, x, y){
  const last = d.aps[d.aps.length - 1], R = {};
  BANDS.forEach(b => { const L = last && last.radios[b]; R[b] = L ? clone(L) : {on:b !== "6", ch:b === "2.4" ? 1 : b === "5" ? 36 : 5, w:b === "2.4" ? 20 : b === "5" ? num(d.cfg.w5, 40) : num(d.cfg.w6, 80), tx:b === "2.4" ? 14 : 20, maxTx:b === "2.4" ? 20 : 23, gain:b === "2.4" ? 3 : 5}; });
  const a = {id:uid("d"), name:nextAPName(d), floor:f.id, x:r1(x), y:r1(y), h:last ? last.h : 3, mount:last ? last.mount : "ceiling", status:"planned", radios:R, model:last ? last.model : "", ip:"", mac:"", serial:"", note:"", cable:"", vlans:last ? last.vlansOwn || "" : "", vlansOwn:last ? last.vlansOwn || "" : "", sw:"", swId:"", port:""};
  if (last) a.__tpl = last.id;
  return a;
}
const ACT = {
  addFloor(){ const b = B(); let id; edit(() => { id = uid("f"); b.floors.push({id, name:gt("floorN",{n:b.floors.length + 1}), lvl:b.floors.length}); normBuilding(b); b.floors[b.floors.length - 1].plan.color = Object.keys(FC)[(b.floors.length - 1) % 6]; UI.sel = {type:"wf", id}; }); },
  floorUp(){ const d = D(), i = d.floors.findIndex(f => f.id === S()); if (S() === OUT_FLOOR) return; if (i > 0) commit(() => { [d.floors[i-1], d.floors[i]] = [d.floors[i], d.floors[i-1]]; }); },
  floorDown(){ const d = D(), i = d.floors.findIndex(f => f.id === S()); if (S() === OUT_FLOOR || (d.floors[i + 1] || {}).id === OUT_FLOOR) return; if (i >= 0 && i < d.floors.length - 1) commit(() => { [d.floors[i+1], d.floors[i]] = [d.floors[i], d.floors[i+1]]; }); },
  async loadImg(){ const d = D(), s = find(d, S()); if (!s) return; const id = await pickImage(); if (id) commit(() => { s.f.img = id; }); },
  rmImg(){ const d = D(), s = find(d, S()); if (s) commit(() => { s.f.img = null; s.f.calibrated = false; }); },
  rmIdf(){ const d = D(), s = find(d, S()); if (s) commit(() => { s.f.idf = null; }); },
  dupSel(){ wifiDup(); }, delSel(){ wifiDel(); },
  autoChan(){ const d = D(); let done; commit(() => { done = autoChan(d, BANDS); }); toast("📡 " + t("autoChanDone",{b:done.map(b => b + " GHz").join(", ") || "—", dfs:d.cfg.dfs ? "DFS ✓" : "DFS ✗"})); },
  placeAp(){ const s0 = UI.sel; if (!s0) return; placeId = s0.id; tool = "select"; UI.tabs.wifi = "plan"; toast("📍 " + t("placeHint")); render(); },
  ssidAdd(){ const d = D(); commit(() => { d.tables.ssid.push({ssid:"", purpose:"", vlan:"", band:"2.4G / 5G", sec:"WPA2/WPA3"}); }); },
  ssidDel(el){ const d = D(), i = +el.dataset.r; commit(() => { d.tables.ssid.splice(i, 1); }); },
  editNotes(){ editList("notes", t("notesHdr")); }, editEquip(){ editList("equip", t("eqHdr")); }
};
function editList(key, title){
  modal(`<h3>✎ ${esc(title)}</h3><label class="fld"><span>${esc(t("notesHint"))}</span><textarea id="wl-t" rows="8">${esc(D()[key].join("\n"))}</textarea></label><div class="mfoot"><button class="btn" data-m="close">${esc(gt("cancel"))}</button><button class="btn pri" data-m="ok">${esc(gt("save"))}</button></div>`,
    {ok:() => { const v = $("#wl-t").value.split("\n").map(s => s.trim()).filter(Boolean); closeModal(); const d = D(); commit(() => { d[key] = v; }); }});
}
function wifiDup(){ const d = D(), s = find(d, S()); if (!s) return;
  if (s.kind === "room"){ const r = Object.assign(clone(s.o), {id:uid("r"), x:r1(s.o.x + 1), y:r1(s.o.y + 1)}); commit(() => { s.f.rooms.push(r); setSel(r.id); }); }
  if (s.kind === "wall"){ const w = Object.assign(clone(s.o), {id:uid("w"), x1:r1(s.o.x1 + .5), x2:r1(s.o.x2 + .5), y1:r1(s.o.y1 + .5), y2:r1(s.o.y2 + .5)}); commit(() => { s.f.walls.push(w); setSel(w.id); }); }
  if (s.kind === "ap"){ const a = Object.assign(clone(s.o), {id:uid("d"), name:nextAPName(d), ip:"", mac:"", serial:"", x:r1(s.o.x + 2)}); a.radios = clone(s.o.radios); a.__tpl = s.o.id; clampAP(d, a); commit(() => { d.aps.push(a); UI.sel = {type:"dev", id:a.id}; }); } }
async function wifiDel(){ const d = D(), s = find(d, S()); if (!s) return;
  if (s.kind === "floor"){ if (s.o.id === OUT_FLOOR) return; if (!await uiConfirm(t("confDelFloor",{n:fName(s.o)}), gt("delete"), true)) return; commit(() => { d.floors = d.floors.filter(f => f.id !== s.o.id); UI.sel = null; }); }
  else if (s.kind === "room") commit(() => { s.f.rooms = s.f.rooms.filter(r => r.id !== s.o.id); UI.sel = null; });
  else if (s.kind === "wall") commit(() => { s.f.walls = s.f.walls.filter(r => r.id !== s.o.id); UI.sel = null; });
  else if (s.kind === "survey") commit(() => { s.f.survey = s.f.survey.filter(r => r.id !== s.o.id); UI.sel = null; });
  else { if (!await uiConfirm(gt("delDevConf",{n:s.o.name}), gt("delete"), true)) return; commit(() => { d.aps = d.aps.filter(a => a.id !== s.o.id); UI.sel = null; }); } }
function setTool(k){ tool = k; pend = null; placeId = null; if (k !== "measure") mline = null; UI.tabs.wifi = "plan"; render(); }
function wifiKey(e){
  if (e.ctrlKey || e.metaKey || e.altKey){ if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "d" && S()){ e.preventDefault(); wifiDup(); } return; }
  const K = {v:"select", r:"room", w:"wall", d:"door", n:"window", a:"ap", s:"survey", m:"measure"}[e.key.toLowerCase()];
  if (K){ e.preventDefault(); setTool(K); return; }
  const d = D(), s = find(d, S()); if (!s) return;
  if (e.key === "Delete" || e.key === "Backspace"){ e.preventDefault(); wifiDel(); return; }
  if (e.key.startsWith("Arrow") && s.kind !== "floor"){ e.preventDefault(); const st = e.shiftKey ? .1 : .5, dx = e.key === "ArrowLeft" ? -st : e.key === "ArrowRight" ? st : 0, dy = e.key === "ArrowUp" ? -st : e.key === "ArrowDown" ? st : 0;
    commit(() => { const o = s.o; if (s.kind === "wall"){ o.x1 = r1(o.x1 + dx); o.x2 = r1(o.x2 + dx); o.y1 = r1(o.y1 + dy); o.y2 = r1(o.y2 + dy); } else { o.x = r1(o.x + dx); o.y = r1(o.y + dy); } if (s.kind === "ap") clampAP(d, o); }); }
}

/* ---------- pointer interaction ---------- */
function redrawFloor(d, f, step){ const ov = document.querySelector(`svg[data-ov="${f.id}"]`); if (ov) ov.innerHTML = overSvg(d, f); drawHeat(d, f, step); }
function ptOf(e, ov, f){ const rect = ov.getBoundingClientRect(); return {x:r1((e.clientX - rect.left) / rect.width * f.wm), y:r1((e.clientY - rect.top) / rect.height * f.hm)}; }
function ortho(p, q){ return Math.abs(q.x - p.x) >= Math.abs(q.y - p.y) ? {x:q.x, y:p.y} : {x:p.x, y:q.y}; }
async function toolClick(e, d, f, ov){
  let p = ptOf(e, ov, f);
  if (tool === "ap"){ const a = newAP(d, f, p.x, p.y); clampAP(d, a); commit(() => { d.aps.push(a); UI.sel = {type:"dev", id:a.id}; }); return; }
  if (tool === "idf"){ tool = "select"; commit(() => { f.idf = {x:p.x, y:p.y}; setSel(f.id); }); return; }
  if (tool === "survey"){ const v = await uiPrompt(t("svAsk",{b:d.view.band}), "-65", "number"); if (v === null) return; commit(() => { const sp = {id:uid("s"), name:"P" + (f.survey.length + 1), x:p.x, y:p.y, band:d.view.band, rssi:num(v, -65), ap:"", note:""}; f.survey.push(sp); setSel(sp.id); }); return; }
  if (["wall","door","window"].includes(tool)){
    if (!pend || pend.f !== f.id){ pend = {f:f.id, x:p.x, y:p.y}; redrawFloor(d, f, 6); return; }
    if (e.shiftKey) p = ortho(pend, p);
    if (Math.hypot(p.x - pend.x, p.y - pend.y) < .2) return;
    const w = {id:uid("w"), x1:pend.x, y1:pend.y, x2:p.x, y2:p.y, kind:tool, mat:curMat()};
    pend = tool === "wall" ? {f:f.id, x:p.x, y:p.y} : null;
    commit(() => { f.walls.push(w); }); return; }
  if (tool === "calib" || tool === "measure"){
    if (!pend || pend.f !== f.id){ pend = {f:f.id, x:p.x, y:p.y}; mline = null; redrawFloor(d, f, 6); return; }
    if (e.shiftKey) p = ortho(pend, p);
    const dm = Math.hypot(p.x - pend.x, p.y - pend.y), q = pend; pend = null;
    if (tool === "measure"){ mline = {f:f.id, x1:q.x, y1:q.y, x2:p.x, y2:p.y}; redrawFloor(d, f, 6); toast("📐 " + r1(dm) + " m"); return; }
    if (dm < .1) return;
    const v = await uiPrompt(t("calAsk",{m:r1(dm)}), String(r1(dm)), "number"); if (v === null || num(v) <= 0){ render(); return; }
    const k = num(v) / dm; tool = "select";
    commit(() => { f.wm = r1(f.wm * k); f.hm = r1(f.hm * k); const sc = o => { ["x","y","w","h","x1","y1","x2","y2"].forEach(z => { if (typeof o[z] === "number") o[z] = r1(o[z] * k); }); };
      f.rooms.forEach(sc); f.walls.forEach(sc); f.survey.forEach(sc); if (f.idf) sc(f.idf); d.aps.filter(a => a.floor === f.id).forEach(sc); f.calibrated = true; });
    toast("📏 " + t("calDone",{w:f.wm, h:f.hm})); return; }
}
const onPlan = () => UI.app === "wifi" && curTab().id === "plan";
let lastClick = null;
function wifiWire(){
  document.addEventListener("click", e => { if (UI.app !== "wifi") return;
    const tb = e.target.closest("[data-tool]"); if (tb){ setTool(tb.dataset.tool); return; }
    const wp = e.target.closest("[data-wplace]"); if (wp){ placeId = placeId === wp.dataset.wplace ? null : wp.dataset.wplace; tool = "select"; render(); return; }
    const wa = e.target.closest("[data-wa]"); if (wa && ACT[wa.dataset.wa]){ ACT[wa.dataset.wa](wa); return; }
    const cs = e.target.closest("[data-wcsv]"); if (cs){ CSV[cs.dataset.wcsv](); return; }
    if (e.target.closest("#modal,#drawer,#pal,#hdr,#ptabs,#btabs")) return;
    const g = e.target.closest("[data-wgo]"); if (g){ UI.tabs.wifi = "plan"; setSel(g.dataset.wgo); render(); reveal(UI.sel); return; }
    const fc = e.target.closest("[data-fl]"); if (fc){ setSel(fc.dataset.fl); render(); return; }
    const ft = e.target.closest("[data-wfl]"); if (ft){ UI.wfFloor = ft.dataset.wfl; render(); } });
  document.addEventListener("change", e => { if (UI.app !== "wifi") return; const el = e.target;
    if (el.dataset.wv){ const d = D(), k = el.dataset.wv, v = el.type === "checkbox" ? el.checked : el.value;
      if (k === "mat"){ lastMat[tool] = v; return; }
      commit(() => { if (k === "prof") d.cfg.prof = v; else if (k === "op") d.view.op = num(v, 70); else d.view[k] = v; }); return; }
    if (el.dataset.wt){ const [i, k] = el.dataset.wt.split(":"), d = D(); commit(() => { d.tables.ssid[+i][k] = el.value.trim(); }); return; }
    if (el.dataset.wr){ const [bd, f] = el.dataset.wr.split(":"), dv = UI.sel && devById(B(), UI.sel.id); if (!dv) return;
      edit(() => { const r = dv.ap.radios[bd]; r[f] = f === "on" ? el.checked : num(el.value, r[f]); if (f === "tx") r.tx = clamp(r.tx, 1, num(r.maxTx, 30)); }); return; }
    if (el.dataset.wc){ const F = CFG.find(x => x.k === el.dataset.wc), d = D(); if (F) commit(() => { F.set(d, el.type === "checkbox" ? el.checked : el.value); }); return; }
    if (el.dataset.wp){ const d = D(), k = el.dataset.wp, v = el.value.trim(); commit(() => { const p = d.cfg.pc; if (k === "sec") p.sec = v === "" ? "" : num(v, -70); else p[k] = num(v, p[k]); }); } });
  document.addEventListener("input", e => { const el = e.target.closest('[data-wv="op"]'); if (!el || UI.app !== "wifi") return; const d = D(); d.view.op = num(el.value, 70); d.floors.forEach(f => drawHeat(d, f, 6)); const lb = el.closest("label").querySelector("span"); if (lb) lb.textContent = t("f_op") + " " + el.value + "%"; save(); });
  document.addEventListener("pointerdown", e => {
    if (e.button !== 0 || !onPlan()) return;
    const ov = e.target.closest("svg.over[data-ov]"); if (!ov) return;
    const d = D(), f = d.floors.find(x => x.id === ov.dataset.ov); if (!f) return; const rect = ov.getBoundingClientRect(), k = rect.width / f.wm;
    if (placeId){ e.preventDefault(); const p = ptOf(e, ov, f), id = placeId, dv = devById(B(), id); placeId = null; if (!dv) return render();
      edit(() => { dv.floor = f.id; dv.ap.x = r1(Math.min(f.wm, Math.max(0, p.x))); dv.ap.y = r1(Math.min(f.hm, Math.max(0, p.y))); UI.sel = {type:"dev", id}; }); return; }
    if (tool === "room"){ e.preventDefault(); const p = ptOf(e, ov, f); drag = {mode:"nr", f, k, x0:e.clientX, y0:e.clientY, p, snap:snapshot(), moved:false, o:{id:uid("r"), x:p.x, y:p.y, w:.1, h:.1, label:t("newRoom"), wall:"drywall", users:0}}; return; }
    if (tool !== "select"){ e.preventDefault(); toolClick(e, d, f, ov); return; }
    const lab = e.target.closest("[data-rlab]");
    if (lab){ const r = f.rooms.find(x => x.id === lab.dataset.rlab), sx = r.pw ? r.w / r.pw : 1, sy = r.ph ? r.h / r.ph : 1; if (r.lx === undefined){ r.lx = r1(r.w / 2 / sx); r.ly = r1(r.h / 2 / sy); }
      setSel(r.id); drag = {f, k, x0:e.clientX, y0:e.clientY, snap:snapshot(), moved:false, mode:"lab", o:r, ox:r.lx, oy:r.ly, sx, sy}; e.preventDefault(); return; }
    const apg = e.target.closest("[data-ap]"), rh = e.target.closest("[data-rh]"), rm = e.target.closest("[data-room]"), wh = e.target.closest("[data-wh]"), wl = e.target.closest("[data-wall]"), sv = e.target.closest("[data-sv]"), idf = e.target.closest("[data-idf]");
    const base = {f, k, x0:e.clientX, y0:e.clientY, snap:snapshot(), moved:false};
    if (apg){ const a = d.aps.find(x => x.id === apg.dataset.ap); UI.sel = {type:"dev", id:a.id}; drag = Object.assign(base, {mode:"ap", o:a, ox:a.x, oy:a.y}); }
    else if (wh){ const [id, end] = wh.dataset.wh.split(":"), w = f.walls.find(x => x.id === id); drag = Object.assign(base, {mode:"we", o:w, end, ox:w["x" + end], oy:w["y" + end]}); }
    else if (sv){ const p = f.survey.find(x => x.id === sv.dataset.sv); setSel(p.id); drag = Object.assign(base, {mode:"pt", o:p, ox:p.x, oy:p.y}); }
    else if (idf){ drag = Object.assign(base, {mode:"pt", o:f.idf, ox:f.idf.x, oy:f.idf.y}); }
    else if (wl){ const w = f.walls.find(x => x.id === wl.dataset.wall); setSel(w.id); drag = Object.assign(base, {mode:"wl", o:w, o0:{x1:w.x1, y1:w.y1, x2:w.x2, y2:w.y2}}); }
    else if (rh){ const r = f.rooms.find(x => x.id === rh.dataset.rh); drag = Object.assign(base, {mode:"rs", o:r, ow:r.w, oh:r.h}); }
    else if (rm){ const r = f.rooms.find(x => x.id === rm.dataset.room); setSel(r.id); drag = Object.assign(base, {mode:"rm", o:r, ox:r.x, oy:r.y}); }
    else {
      // Double click / double tap on an empty spot adds an access point (tracked here because the first click re-renders the plan).
      const now = Date.now(), lc = lastClick;
      if (lc && now - lc.t < 400 && Math.hypot(e.clientX - lc.x, e.clientY - lc.y) < 12 && lc.f === f.id){
        lastClick = null; const p = ptOf(e, ov, f), a = newAP(d, f, p.x, p.y); clampAP(d, a); commit(() => { d.aps.push(a); UI.sel = {type:"dev", id:a.id}; }); return; }
      lastClick = {t:now, x:e.clientX, y:e.clientY, f:f.id};
      if (UI.sel){ UI.sel = null; render(); } return; }
    e.preventDefault(); redrawFloor(d, f, 12);
  });
  document.addEventListener("pointermove", e => {
    if (!drag){ if (pend && ["wall","door","window","calib","measure"].includes(tool)){ const ov = document.querySelector(`svg[data-ov="${pend.f}"]`), ln = ov && ov.querySelector(".wprev"); if (!ln) return;
        const f = D().floors.find(x => x.id === pend.f); let p = ptOf(e, ov, f); if (e.shiftKey) p = ortho(pend, p); const s = PW / f.wm; ln.setAttribute("x2", p.x * s); ln.setAttribute("y2", p.y * s);
        const tx = ov.querySelector(".wlen"); if (tx){ tx.setAttribute("x", p.x * s + 8); tx.setAttribute("y", p.y * s - 8); tx.textContent = r1(Math.hypot(p.x - pend.x, p.y - pend.y)) + " m"; } } return; }
    const dx = (e.clientX - drag.x0) / drag.k, dy = (e.clientY - drag.y0) / drag.k;
    if (!drag.moved && Math.hypot(e.clientX - drag.x0, e.clientY - drag.y0) < 3) return; drag.moved = true;
    const o = drag.o, f = drag.f;
    if (drag.mode === "ap"){ o.x = r1(Math.min(f.wm, Math.max(0, drag.ox + dx))); o.y = r1(Math.min(f.hm, Math.max(0, drag.oy + dy))); }
    else if (drag.mode === "rm" || drag.mode === "pt"){ o.x = r1(drag.ox + dx); o.y = r1(drag.oy + dy); }
    else if (drag.mode === "lab"){ o.lx = r1(drag.ox + dx / drag.sx); o.ly = r1(drag.oy + dy / drag.sy); }
    else if (drag.mode === "we"){ let q = {x:r1(drag.ox + dx), y:r1(drag.oy + dy)}; if (e.shiftKey){ const oth = drag.end === "1" ? {x:o.x2, y:o.y2} : {x:o.x1, y:o.y1}; q = ortho(oth, q); } o["x" + drag.end] = q.x; o["y" + drag.end] = q.y; }
    else if (drag.mode === "wl"){ const z = drag.o0; o.x1 = r1(z.x1 + dx); o.x2 = r1(z.x2 + dx); o.y1 = r1(z.y1 + dy); o.y2 = r1(z.y2 + dy); }
    else if (drag.mode === "nr"){ const p = drag.p; o.x = r1(Math.min(p.x, p.x + dx)); o.y = r1(Math.min(p.y, p.y + dy)); o.w = Math.max(.1, r1(Math.abs(dx))); o.h = Math.max(.1, r1(Math.abs(dy))); if (!f.rooms.includes(o)) f.rooms.push(o); }
    else { o.w = Math.max(.5, r1(drag.ow + dx)); o.h = Math.max(.5, r1(drag.oh + dy)); }
    redrawFloor(D(), f, 12);
  });
  const up = cancel => { if (!drag) return; const g = drag; drag = null;
    if (cancel){ FCD = null; render(); return; }
    if (g.mode === "nr"){ if (!g.moved || g.o.w < .3 || g.o.h < .3){ g.f.rooms = g.f.rooms.filter(r => r !== g.o); render(); return; } setSel(g.o.id); tool = "select"; }
    if (g.moved){ pushUndo(g.snap); syncOut(); normBuilding(B()); persist(); } render(); };
  document.addEventListener("pointerup", () => up(false));
  document.addEventListener("pointercancel", () => up(true));
}

/* ---------- warnings ---------- */
function wifiWarnings(d){
  const W = [], ids = {}, P = prof(d), cap = {}, push = (w, key) => { cap[key] = (cap[key] || 0) + 1; if (cap[key] <= 6) W.push(w); };
  const noModel = [];
  d.aps.forEach(a => { const n = String(a.name).trim(); if (n){ if (ids[n]) W.push(["err", t("w_apDup",{n}), a.id]); ids[n] = 1; }
    if (a.status === "removed") return;
    if (!a.model) noModel.push(a.name);
    BANDS.forEach(b => { const r = radio(a, b); if (!r.on) return;
      if (r.none) W.push(["err", t("w_noBand",{n:a.name, b}), a.id]);
      else if (num(r.tx) > num(r.maxTx, 99)) W.push(["err", t("w_txMax",{n:a.name, b, t:r.tx, m:r.maxTx}), a.id]);
      if (b === "2.4" && !CH24.includes(num(r.ch))) push(["", t("w_ch24",{n:a.name, c:r.ch}), a.id], "ch24");
      if (b === "5" && isDFS(num(r.ch)) && !d.cfg.dfs) push(["info", t("w_dfs",{n:a.name, c:r.ch}), a.id], "dfs");
      if (b === "6" && (num(r.ch) - 5) % 16 !== 0 && num(r.w) === 20) push(["info", t("w_psc",{n:a.name, c:r.ch}), a.id], "psc"); });
    const L = cableLen(d, a); if (L !== null && L > 90) W.push(["err", t("w_cable",{n:a.name, l:L}), a.id]);
    if (!a.swId) push(["info", t("w_apNoSw",{n:a.name}), a.id], "nosw");
  });
  if (noModel.length) W.push(["info", t("w_apNoModel",{n:noModel.slice(0, 5).join(", ") + (noModel.length > 5 ? " … (+" + (noModel.length - 5) + ")" : "")})]);
  BANDS.forEach(b => { const L = d.aps.filter(a => radioOn(a, b));
    for (let i = 0; i < L.length; i++) for (let j = i + 1; j < L.length; j++){ const a = L[i], c = L[j]; if (!overlap(rspan(a, b), rspan(c, b))) continue;
      const v = Math.max(apPairLoss(d, a, c, b), apPairLoss(d, c, a, b)); if (v >= -67) push(["", t("w_cci",{a:a.name, c:c.name, b, ch:radio(a, b).ch, v:Math.round(v)}), a.id], "cci" + b); } });
  const carried = new Set(); d.aps.forEach(a => String(a.vlans || "").split(/[,; ]+/).filter(Boolean).forEach(v => carried.add(v.trim())));
  const sb = {"2.4":0, "5":0, "6":0};
  d.tables.ssid.forEach(r => { const v = String(r.vlan || "").trim(), sc = String(r.sec || "").trim(), bs = String(r.band || "");
    if (v && d.aps.length && carried.size && !carried.has(v)) W.push(["", t("w_vlanMiss",{s:r.ssid || "?", v})]);
    if (r.ssid && (!sc || /^[-–—]+$/.test(sc) || /open|açıq|açık|откр/i.test(sc))) W.push(["err", t("w_noSec",{s:r.ssid})]);
    if (r.ssid && /\bWEP\b|TKIP|\bWPA\b(?![23])/i.test(sc)) W.push(["err", t("w_wep",{s:r.ssid})]);
    if (r.ssid && /6\s*G/i.test(bs) && !/WPA3|OWE|Enhanced Open/i.test(sc)) W.push(["err", t("w_6sec",{s:r.ssid})]);
    if (/2\.4/.test(bs) || !bs) sb["2.4"]++; if (/\b5\s*G|\/\s*5|^5/i.test(bs) || !bs) sb["5"]++; if (/6\s*G/i.test(bs)) sb["6"]++; });
  BANDS.forEach(b => { if (sb[b] > 4) W.push(["", t("w_ssidN",{n:sb[b], b})]); });
  const S2 = swLoad(d), b0 = B(); Object.keys(S2).forEach(id => { const sw = devById(b0, id); if (!sw) return; const bud = num(sw.params.poeBudget), pts = num(sw.params.poePorts || sw.ports);
    if (bud && S2[id].w > bud) W.push(["err", t("w_poe",{s:devLabel(sw), w:r1(S2[id].w), b:bud}), id]);
    if (pts && S2[id].n > pts) W.push(["err", t("w_ports",{s:devLabel(sw), n:S2[id].n, p:pts}), id]); });
  const CL = clientLoad(d); d.aps.forEach(a => { const c = Math.round(CL[a.id] || 0); if (c > d.cfg.cpa) W.push(["", t("w_load",{n:a.name, c, m:d.cfg.cpa}), a.id]); });
  d.floors.forEach(f => { const nm = fName(f);
    if (!d.aps.some(a => a.floor === f.id && a.status !== "removed")){ W.push(["info", t("w_noAP",{f:nm}), f.id]); return; }
    const E = evalFloor(d, f, d.view.band); if (E.pct < P.cover) W.push(["", t("w_cover2",{f:nm, p:E.pct, c:P.cover, pr:t("pr_" + d.cfg.prof), b:d.view.band}), f.id]);
    f.rooms.forEach(r => { const q = E.rooms[r.id]; if (q && num(r.users) > 0 && q.pct < 50) push(["", t("w_room",{r:rLabel(r), f:fShort(f), p:q.pct}), r.id], "room"); });
    if (f.img && !f.calibrated) W.push(["info", t("w_calib",{f:nm}), f.id]);
    if (!f.idf) push(["info", t("w_noIdf",{f:nm}), f.id], "idf");
    f.survey.forEach(p => { const pr = predictAt(d, f, p.band, p.x, p.y); if (pr !== null && Math.abs(num(p.rssi) - pr) > 8) push(["", t("w_survey",{p:p.name || "?", m:num(p.rssi), pr:Math.round(pr)}), p.id], "sv"); });
  });
  const U = unplacedAps(); if (U.length) W.push(["info", t("w_unplaced",{n:U.length})]);
  Object.keys(cap).forEach(k => { if (cap[k] > 6) W.push(["info", t("w_more",{n:cap[k] - 6})]); });
  return W;
}

/* ---------- settings tab ---------- */
const WOPTS = [["20","20 MHz"],["40","40 MHz"],["80","80 MHz"],["160","160 MHz"]];
const CFG = [
  {k:"n", label:"f_n", get:d => d.cfg.n, set:(d, v) => { d.cfg.n = clamp(num(v, 3), 1.6, 5); }},
  {k:"floorH", label:"f_floorH", get:d => d.cfg.floorH, set:(d, v) => { d.cfg.floorH = Math.max(2, num(v, 3.5)); }},
  {k:"clientH", label:"f_clientH", get:d => d.cfg.clientH, set:(d, v) => { d.cfg.clientH = Math.max(0, num(v, 1)); }},
  {k:"cg", label:"f_cg", get:d => d.cfg.cg, set:(d, v) => { d.cfg.cg = num(v, 0); }},
  {k:"fl24", label:"f_fl24", get:d => d.cfg.fl["2.4"], set:(d, v) => { d.cfg.fl["2.4"] = num(v, 14); }},
  {k:"fl5", label:"f_fl5", get:d => d.cfg.fl["5"], set:(d, v) => { d.cfg.fl["5"] = num(v, 18); }},
  {k:"fl6", label:"f_fl6", get:d => d.cfg.fl["6"], set:(d, v) => { d.cfg.fl["6"] = num(v, 22); }},
  {k:"nf24", label:"f_nf24", get:d => d.cfg.nf["2.4"], set:(d, v) => { d.cfg.nf["2.4"] = num(v, -92); }},
  {k:"nf5", label:"f_nf5", get:d => d.cfg.nf["5"], set:(d, v) => { d.cfg.nf["5"] = num(v, -95); }},
  {k:"nf6", label:"f_nf6", get:d => d.cfg.nf["6"], set:(d, v) => { d.cfg.nf["6"] = num(v, -95); }},
  {k:"dfs", label:"f_dfs", type:"chk", get:d => d.cfg.dfs, set:(d, v) => { d.cfg.dfs = !!v; }},
  {k:"w5", label:"f_w5", type:"sel", opts:WOPTS, get:d => d.cfg.w5, set:(d, v) => { d.cfg.w5 = num(v, 40); }},
  {k:"w6", label:"f_w6", type:"sel", opts:WOPTS, get:d => d.cfg.w6, set:(d, v) => { d.cfg.w6 = num(v, 80); }},
  {k:"css", label:"f_css", type:"sel", opts:[["1","1x1"],["2","2x2"],["3","3x3"],["4","4x4"]], get:d => d.cfg.css, set:(d, v) => { d.cfg.css = num(v, 2); }},
  {k:"cpa", label:"f_cpa", get:d => d.cfg.cpa, set:(d, v) => { d.cfg.cpa = Math.max(1, num(v, 50)); }},
  {k:"dpu", label:"f_dpu", get:d => d.cfg.dpu, set:(d, v) => { d.cfg.dpu = Math.max(0, num(v, 1.5)); }},
  {k:"vert", label:"f_vert", get:d => d.cfg.vert, set:(d, v) => { d.cfg.vert = Math.max(0, num(v, 4)); }},
  {k:"slack", label:"f_slack", get:d => d.cfg.slack, set:(d, v) => { d.cfg.slack = Math.max(0, num(v, 3)); }}
];
function settingsView(){
  const d = D(), p = d.cfg.pc, custom = d.cfg.prof === "custom";
  const f = F => F.type === "chk" ? `<label class="chk"><input type="checkbox" data-wc="${F.k}"${F.get(d) ? " checked" : ""}> ${esc(t(F.label))}</label>`
    : F.type === "sel" ? `<label class="fld"><span>${esc(t(F.label))}</span><select data-wc="${F.k}">${F.opts.map(([a, l]) => opt(a, l, String(F.get(d)))).join("")}</select></label>`
    : `<label class="fld"><span>${esc(t(F.label))}</span><input type="number" step="any" data-wc="${F.k}" value="${esc(F.get(d))}"></label>`;
  const pi = (k, l, ph) => `<label class="fld"><span>${esc(t(l))}</span><input data-wp="${k}" value="${esc(p[k] ?? "")}"${ph ? ` placeholder="${ph}"` : ""}${custom ? "" : " disabled"}></label>`;
  return `<div class="card"><h3>🎯 ${esc(t("tab_req"))}</h3><p class="muted small">${esc(t("reqHint"))}</p>
    <label class="fld" style="max-width:320px"><span>${esc(t("f_prof"))}</span><select data-wv="prof">${[...Object.keys(PROF), "custom"].map(x => opt(x, t("pr_" + x), d.cfg.prof)).join("")}</select></label>
    ${custom ? "" : `<p class="muted small">${esc(t("customHint"))}</p>`}
    <div class="wgrid4">${pi("rssi","pc_rssi")}${pi("snr","pc_snr")}${pi("sec","pc_sec","—")}${pi("cnt","pc_cnt")}${pi("cntR","pc_cntR")}${pi("cci","pc_cci")}${pi("cover","pc_cover")}</div>
    <div class="scroll"><table class="t" style="margin-top:8px"><tr><th></th><th>RSSI</th><th>SNR</th><th>${esc(t("pc_secS"))}</th><th>${esc(t("pc_cntS"))}</th><th>CCI</th><th>%</th></tr>${Object.entries(PROF).map(([k, q]) => `<tr${d.cfg.prof === k ? ' class="on"' : ""}><td><b>${esc(t("pr_" + k))}</b></td><td class="c">${q.rssi}</td><td class="c">${q.snr}</td><td class="c">${q.sec || "—"}</td><td class="c">${q.cnt} @ ${q.cntR}</td><td class="c">≤${q.cci}</td><td class="c">${q.cover}</td></tr>`).join("")}</table></div></div>
    <div class="card"><h3>⚙ ${esc(t("calcSet"))}</h3><div class="wgrid4">${CFG.filter(F => F.type !== "chk").map(f).join("")}</div>${CFG.filter(F => F.type === "chk").map(f).join("")}</div>`;
}
function apsView(){
  const d = D();
  return `${panel(t("apHdr"), apTable(d), `<button class="btn small" data-wcsv="ap">⤓ CSV</button>`)}
    ${panel(t("ssidHdr"), ssidTable(d), `<button class="btn small" data-wcsv="ssid">⤓ CSV</button>`)}
    <div class="wcols">${swPanel(d)}${bomPanel(d)}</div>${surveyPanel(d)}
    <div class="wcols">${panel(t("ovHdr"), overview(d))}<div>${panel(t("eqHdr"), notesBody(d.equip), `<button class="btn small" data-wa="editEquip">✎</button>`)}${panel(t("notesHdr"), notesBody(d.notes), `<button class="btn small" data-wa="editNotes">✎</button>`)}</div></div>`;
}
function docBody(){
  const d = syncIn(), b = d.view.band;
  return `<div class="wdoc">${d.floors.length ? `<p class="muted small">${esc(t("v_" + d.view.mode))}, ${b} GHz · ${esc(t("pr_" + d.cfg.prof))}</p>${plansHtml(d, true)}<div style="margin:8px 0">${legendHtml(d)}</div>` : ""}
    ${resultsPanel(d)}${panel(t("apHdr"), apTable(d))}${d.tables.ssid.length ? panel(t("ssidHdr"), tableRO([{k:"ssid", label:"SSID", b:1}, {k:"purpose", label:t("c_purpose")}, {k:"vlan", label:"VLAN", c:1}, {k:"band", label:"Band", c:1}, {k:"sec", label:t("c_sec")}], d.tables.ssid)) : ""}
    ${bomPanel(d)}${d.notes.length ? panel(t("notesHdr"), notesBody(d.notes)) : ""}</div>`;
}

/* ---------- exports ---------- */
async function exportHeat(fid){
  const d = D(), f = d.floors.find(x => x.id === fid); if (!f) return;
  const s = PW / f.wm, H = Math.round(f.hm * s), Z = 3, c = document.createElement("canvas"); c.width = PW * Z; c.height = (H + 40) * Z;
  const x = c.getContext("2d"); x.fillStyle = "#fff"; x.fillRect(0, 0, c.width, c.height);
  if (f.img && assetURL(f.img)){ const im = new Image(); im.src = assetURL(f.img); await im.decode().catch(() => {}); x.globalAlpha = num(f.op, 60) / 100; x.drawImage(im, 0, 0, PW * Z, H * Z); x.globalAlpha = 1; }
  const hc = document.createElement("canvas"); hc.width = PW * Z; hc.height = H * Z; paintHeat(d, f, 3, hc, d.view.mode, d.view.band); x.drawImage(hc, 0, 0);
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${PW}" height="${H}" viewBox="0 0 ${PW} ${H}" font-family="Segoe UI,Arial,sans-serif">${overSvg(d, f, true)}</svg>`;
  const im2 = new Image(); im2.src = "data:image/svg+xml;charset=utf-8," + encodeURIComponent(svg); await im2.decode().catch(() => {}); x.drawImage(im2, 0, 0, PW * Z, H * Z);
  x.fillStyle = "#1d2433"; x.font = `bold ${13 * Z}px Segoe UI, Arial`; x.fillText(`${fName(f)} — ${t("v_" + d.view.mode)}, ${d.view.band} GHz — ${t("pr_" + d.cfg.prof)}: ${evalFloor(d, f, d.view.band).pct}%`, 8 * Z, (H + 26) * Z);
  const blob = await new Promise(r => c.toBlob(r, "image/png"));
  saveBinary(fileSafe(d.name) + " - " + fileSafe(fShort(f)) + " - " + d.view.mode + "-" + d.view.band + "GHz.png", blob, "png");
}
const CSV = {
  ap(){ const d = D(), CL = clientLoad(d);
    exportCSV(t("ex_ap"), ["AP", gt("f_status"), t("c_floorS"), t("c_room"), "X (m)", "Y (m)", gt("f_model"), t("f_mount"), t("f_h"), ...BANDS.flatMap(b => [`${b} on`, `${b} ch`, `${b} MHz`, `${b} dBm`]), "Switch", "Port", "VLAN", "IP", "MAC", gt("f_serial"), t("c_cable") + " (m)", "PoE (W)", t("c_cl"), t("f_note")],
      d.aps.map(a => { const f = d.floors.find(x => x.id === a.floor), rm = roomAt(d, a); return [a.name, gt("st_" + a.status), fShort(f), rm ? rLabel(rm) : "", a.x, a.y, a.model, t(a.mount === "wall" ? "m_wall" : "m_ceil"), a.h,
        ...BANDS.flatMap(b => { const r = radio(a, b); return [radioOn(a, b) ? "✓" : "", r.ch, r.w, r.tx]; }), a.sw, a.port, a.vlans, a.ip, a.mac, a.serial, cableLen(d, a) ?? "", MOD(a).poe, Math.round(CL[a.id] || 0), a.note]; })); },
  ssid(){ const d = D(); exportCSV(t("ex_ssid"), ["SSID", t("c_purpose"), "VLAN", "Band", t("c_sec")], d.tables.ssid.map(r => [r.ssid, r.purpose, r.vlan, r.band, r.sec])); },
  bom(){ const d = D(); exportCSV(t("ex_bom"), [t("c_item"), t("c_spec"), t("c_qty")], bomRows(d).map(r => [r.item, r.spec, r.qty])); },
  rooms(){ const d = D(), b = d.view.band, R = []; d.floors.forEach(f => { const E = evalFloor(d, f, b); f.rooms.forEach(r => { const q = E.rooms[r.id]; R.push([fShort(f), rLabel(r), t("mat_" + r.wall), r1(r.w * r.h), num(r.users), q ? q.pct : ""]); }); });
    exportCSV(t("ex_rooms"), [t("c_floorS"), t("c_room"), t("c_mat"), "m²", t("c_users"), t("c_pass",{p:prof(d).cover}) + ` (${b} GHz)`], R); },
  survey(){ const d = D(); exportCSV(t("ex_survey"), ["#", t("c_floorS"), "Band", t("c_meas"), t("c_pred"), "Δ dB", t("c_note")], surveyRows(d).map(r => [r.n, r.f, r.band, r.m, r.p, r.dl, r.note])); }
};
function reveal(s){ if (!s) return; const d = D(), a = d.aps.find(x => x.id === s.id), fl = a ? a.floor : (d.floors.find(f => f.id === s.id || f.rooms.some(r => r.id === s.id)) || {}).id; if (fl && fl !== UI.wfFloor){ UI.wfFloor = fl; render(); } setTimeout(() => { const el = document.querySelector(`[data-ap="${s.id}"],[data-room="${s.id}"],[data-wall="${s.id}"],[data-fl="${s.id}"],[data-sv="${s.id}"]`); if (el) el.scrollIntoView({block:"center", behavior:"smooth"}); }, 40); }

registerApp({
  id:"wifi", name:"app_wifi", desc:"app_wifi_d", docName:"doc_wifi", color:"#138a8a",
  glyph:`<path d="M10 21a20 20 0 0 1 28 0M15 27a12 12 0 0 1 18 0" stroke="#fff" stroke-width="3.5" fill="none" stroke-linecap="round"/><path d="M20 32a5 5 0 0 1 8 0" stroke="#ffb703" stroke-width="3.5" fill="none" stroke-linecap="round"/><circle cx="24" cy="36" r="2.5" fill="#fff"/>`,
  tabs:[
    {id:"plan", label:"tabPlan", icon:"🗺", palette:() => B().floors.length ? wifiPalette() : "",
      render(){ const d = syncIn(); return `${warnBox(wifiWarnings(d))}${plansHtml(d)}${d.floors.length ? `<p class="dghint">ⓘ ${esc(t("dblHint"))}</p>` + resultsPanel(d) : ""}`; },
      tour:() => [{sel:"#appsw", title:gt("tShellT1"), text:gt("tShell1")}, {sel:'[data-act="addFloor"]', title:t("tWfT1"), text:t("tWf1")}, {sel:"#pal .wtools", title:t("tWfT2"), text:t("tWf2")}, {sel:'#pal [data-wv="mode"]', title:t("tWfT3"), text:t("tWf3")}, {sel:'[data-tab="aps"]', title:t("tWfT4"), text:t("tWf4")}, {sel:'[data-tab="set"]', title:t("tWfT5"), text:t("tWf5")}, tip('#pal [data-tool="calib"]', "tp_wfCalib"), tip('[data-act="autoChan"]', "tp_wfChan"), tip('#pal [data-tool="survey"]', "tp_wfSurvey"), TIPS.warn(), TIPS.help()]},
    {id:"aps", label:"tabAps", icon:"📶", tour:() => [tip('[data-wa="ssidAdd"]', "tp_wfSsid"), TIPS.warn()], render(){ syncIn(); return `${warnBox(wifiWarnings(D()))}${apsView()}`; }},
    {id:"set", label:"tabWset", icon:"🎯", tour:() => [tip('[data-wv="prof"]', "tp_wfProf")], render(){ syncIn(); return settingsView(); }},
    docTab("wifi", docBody)
  ],
  actions(tab){ return [{id:"addFloor", icon:"＋", label:"wfAddFloor", fn:ACT.addFloor}, B().floors.length ? {id:"autoChan", icon:"📡", label:"wfAutoChan", fn:ACT.autoChan} : null, {id:"places", icon:"🏢", label:"places", fn:() => openPlaces()}]; },
  drawer(){ return wifiDrawer(); },
  afterRender(){ if (!FCD) return; const d = FCD.d; d.floors.forEach(f => drawHeat(d, f, 6)); },
  onField(p, v){ wifiField(p, v); },
  onDrawerAct(k, el){ if (ACT[k]) ACT[k](el); },
  onKey(e, tab){ if (tab.id === "plan") wifiKey(e); },
  onEsc(){ if (tool !== "select" || pend || mline || placeId){ tool = "select"; pend = null; mline = null; placeId = null; render(); return true; } return false; },
  exports(){ const d = D(); return [...d.floors.map(f => ({icon:"🖼", label:t("ex_heat",{f:fName(f)}), fn:() => exportHeat(f.id)})),
    {icon:"▦", label:t("ex_ap"), fn:CSV.ap}, {icon:"▦", label:t("ex_ssid"), fn:CSV.ssid}, {icon:"▦", label:t("ex_bom"), fn:CSV.bom}, {icon:"▦", label:t("ex_rooms"), fn:CSV.rooms}, {icon:"▦", label:t("ex_survey"), fn:CSV.survey}]; },
  reveal(s){ if (s && s.type === "dev"){ const dv = devById(B(), s.id); if (dv && dv.kind === "ap"){ UI.tabs.wifi = "plan"; render(); } } reveal(s); },
  guide:() => [[t("gWf1h"), t("gWf1")], [t("gWf2h"), t("gWf2")], [t("gWf3h"), t("gWf3")], [t("gWf4h"), t("gWf4")], [t("gWf5h"), t("gWf5")]]
});
APPS.wifi.init = wifiWire;
window.WIFI = {D, syncIn, evalFloor, cableLen, autoChan};
})();
