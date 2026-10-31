/*! NetWorkKing — © 2026 Ulvi Badalov. Bütün hüquqlar qorunur / All rights reserved. Proprietary — see LICENSE. */
// DXF reader: AutoCAD drawing exchange files (text DXF, R12 … 2018) read in the browser, without any library.
// parse() reads group codes into blocks and entities; flatten() expands block references (INSERT) into world coordinates
// and keeps track of the layer each piece really belongs to; analyze() guesses what each layer is (walls, doors, windows,
// room names, yard …), the drawing units and how many separate floor plans the file holds; build() turns one chosen floor
// into a plan for the Building app: a clean drawing (SVG), rooms, Wi-Fi walls (doors and windows close their wall gaps)
// and outlets found as blocks.
"use strict";
const DXF = (function(){
const D2R = Math.PI / 180;
/* ---------- text decoding ---------- */
function decode(buf){
  const u8 = new Uint8Array(buf), head = new TextDecoder("latin1").decode(u8.subarray(0, 4000));
  const ver = (head.match(/\$ACADVER\s*\r?\n\s*1\s*\r?\n\s*(AC\d+)/) || [])[1] || "";
  const cp = ((head.match(/\$DWGCODEPAGE\s*\r?\n\s*3\s*\r?\n\s*(\S+)/) || [])[1] || "").toLowerCase();
  if (/^\0|^AutoCAD Binary DXF/.test(head)) throw new Error("binary");
  if (ver >= "AC1021"){ try { return new TextDecoder("utf-8", {fatal:true}).decode(u8); } catch(e){} }
  const m = cp.match(/ansi_(\d+)/), enc = m ? "windows-" + m[1] : "windows-1252";
  try { return new TextDecoder(enc).decode(u8); } catch(e){ return new TextDecoder("windows-1252").decode(u8); }
}
const uni = s => s.replace(/\\U\+([0-9a-fA-F]{4})/g, (_, h) => String.fromCharCode(parseInt(h, 16))).replace(/%%[cC]/g, "Ø").replace(/%%[dD]/g, "°").replace(/%%[pP]/g, "±").replace(/%%[uUoO]/g, "");
function mtext(s){
  s = uni(s).replace(/\\P/g, "\n").replace(/\\~/g, " ").replace(/\\S([^;]*?)[\^#\/]([^;]*);/g, "$1/$2")
    .replace(/\\[ACHTQWFfpX][^;\\]*;/g, "").replace(/\\[LlOoKkN]/g, "").replace(/[{}]/g, "").replace(/\\\\/g, "\\");
  return s.replace(/[ \t]+/g, " ").trim();
}
/* ---------- group codes → entities ---------- */
function parse(text){
  const L = text.split(/\r?\n/), n = L.length - 1;
  const doc = {header:{}, blocks:{}, ents:[], layers:{}};
  let i = 0, sec = null, blk = null, cur = null, hv = null;
  const close = () => { if (!cur) return; if (sec === "ENTITIES") doc.ents.push(cur); else if (sec === "BLOCKS" && blk) blk.ents.push(cur); else if (sec === "TABLES" && cur.t === "LAYER" && cur.g[2]) doc.layers[cur.g[2]] = {color:+cur.g[62] || 7, off:+cur.g[62] < 0, frozen:(+cur.g[70] & 1) === 1}; cur = null; };
  while (i < n){
    const c = +L[i], v = L[i + 1]; i += 2;
    if (c === 0){
      close();
      if (v === "SECTION"){ sec = "?"; continue; }
      if (v === "ENDSEC"){ sec = null; continue; }
      if (v === "EOF") break;
      if (sec === "BLOCKS" && v === "BLOCK"){ blk = {name:"", base:[0, 0], flags:0, ents:[]}; cur = {t:"BLOCKHEAD", g:{}, p:[]}; continue; }
      if (sec === "BLOCKS" && v === "ENDBLK"){ blk = null; continue; }
      if (sec === "HEADER") continue;
      cur = {t:v, g:{}, p:[]};
      continue;
    }
    if (sec === "?" && c === 2){ sec = v.trim(); continue; }
    if (sec === "HEADER"){ if (c === 9) hv = v.trim(); else if (hv){ (doc.header[hv] = doc.header[hv] || {})[c] = v.trim(); } continue; }
    if (!cur) continue;
    if (cur.t === "BLOCKHEAD"){ if (c === 2){ blk.name = v; doc.blocks[v] = blk; } else if (c === 10) blk.base[0] = +v; else if (c === 20) blk.base[1] = +v; else if (c === 70) blk.flags = +v; continue; }
    // repeated codes (vertices, MTEXT chunks) are kept in order in p; the last value of each code is in g
    if (c === 10 || c === 20 || c === 42 || c === 11 || c === 21 || c === 3) cur.p.push(c, v);
    cur.g[c] = v;
  }
  close();
  // old-style POLYLINE + VERTEX … SEQEND into one entity
  const join = list => { const out = []; for (let k = 0; k < list.length; k++){ const e = list[k];
      if (e.t === "POLYLINE"){ const vs = []; while (k + 1 < list.length && list[k + 1].t === "VERTEX"){ const q = list[++k]; if (!(+q.g[70] & 16)) vs.push(+q.g[10], +q.g[20], +q.g[42] || 0); } if (k + 1 < list.length && list[k + 1].t === "SEQEND") k++; e.vs = vs; out.push(e); }
      else if (e.t === "ATTRIB" || e.t === "SEQEND" || e.t === "VERTEX") continue; else out.push(e); } return out; };
  doc.ents = join(doc.ents); for (const k in doc.blocks) doc.blocks[k].ents = join(doc.blocks[k].ents);
  return doc;
}
/* ---------- geometry ---------- */
const mul = (A, B) => [A[0] * B[0] + A[2] * B[1], A[1] * B[0] + A[3] * B[1], A[0] * B[2] + A[2] * B[3], A[1] * B[2] + A[3] * B[3], A[0] * B[4] + A[2] * B[5] + A[4], A[1] * B[4] + A[3] * B[5] + A[5]];
const ap = (M, x, y) => [M[0] * x + M[2] * y + M[4], M[1] * x + M[3] * y + M[5]];
const ID = [1, 0, 0, 1, 0, 0], MIRX = [-1, 0, 0, 1, 0, 0];
const ocs = e => +e.g[230] < 0;   // extrusion (0,0,-1): object coordinates are mirrored in X
function arcPts(cx, cy, r, a0, a1){ while (a1 <= a0) a1 += 360; const n = Math.max(2, Math.ceil((a1 - a0) / 12)), P = []; for (let k = 0; k <= n; k++){ const a = (a0 + (a1 - a0) * k / n) * D2R; P.push(cx + r * Math.cos(a), cy + r * Math.sin(a)); } return P; }
function bulgePts(P){ // [x,y,b, x,y,b …] → points with arcs
  const out = [];
  for (let k = 0; k < P.length; k += 3){ out.push(P[k], P[k + 1]); const b = P[k + 2]; if (!b || k + 3 >= P.length + (P.closedBulge ? 3 : 0)) continue;
    const x1 = P[k], y1 = P[k + 1], j = (k + 3) % P.length, x2 = P[j], y2 = P[j + 1], th = 4 * Math.atan(b), d = Math.hypot(x2 - x1, y2 - y1); if (d < 1e-9) continue;
    const r = d / (2 * Math.sin(th / 2)), mx = (x1 + x2) / 2, my = (y1 + y2) / 2, h = r * Math.cos(th / 2), nx = -(y2 - y1) / d, ny = (x2 - x1) / d;
    const cx = mx + nx * h, cy = my + ny * h, a1 = Math.atan2(y1 - cy, x1 - cx), n = Math.max(2, Math.ceil(Math.abs(th) / (12 * D2R)));
    for (let q = 1; q < n; q++){ const a = a1 + th * q / n; out.push(cx + Math.abs(r) * Math.cos(a), cy + Math.abs(r) * Math.sin(a)); } }
  return out;
}
const normLayer = l => String(l || "0").replace(/^.*\$0\$/, "").replace(/^.*\|/, "");
/* ---------- block references → world geometry ---------- */
// segs: polylines {L:layer, p:[x,y…], c:closed}; texts {L,s,x,y,h}; refs: every block reference with its world box
function flatten(doc, opt = {}){
  const segs = [], texts = [], refs = [], LIM = opt.limit || 1500000; let pts = 0;
  // layers switched off or frozen are still read (an electrical drawing often freezes the architect's doors) and marked
  const hidden = l => { const x = doc.layers[l]; return !!(x && (x.off || x.frozen)); }, HN = {}, VN = {}, HID = {add:L => { HN[L] = 1; }};
  let hid = false, TOP = -1, TINS = false, RID = 0; const CH = [];   // CH: the block references a piece sits in, outermost first   // the top-level entity a piece comes from (one tree, one lamp … stays one piece)
  const push = (L, M, P, closed) => { if (pts > LIM || P.length < 4) return; const W = new Array(P.length); for (let k = 0; k < P.length; k += 2){ const q = ap(M, P[k], P[k + 1]); W[k] = q[0]; W[k + 1] = q[1]; } pts += P.length / 2; segs.push({L, p:W, c:!!closed, h:hid, g:TOP, ins:TINS, ch:CH.length ? CH.slice() : null}); if (hid) HN[L] = 1; else VN[L] = 1; return W; };
  function walk(list, M, inL, depth, box, inHid){
    for (const e of list){
      if (!depth){ TOP++; TINS = e.t === "INSERT"; }
      const raw = e.g[8] || "0", L = raw === "0" && inL ? inL : normLayer(raw);
      hid = raw === "0" && inL ? !!inHid : hidden(raw);
      const g = e.g, Mo = ocs(e) ? mul(M, MIRX) : M; let W = null;
      switch (e.t){
        case "LINE": W = push(L, M, [+g[10], +g[20], +g[11], +g[21]]); break;
        case "LWPOLYLINE": { const P = []; let last = null; for (let k = 0; k < e.p.length; k += 2){ const c = +e.p[k], v = +e.p[k + 1]; if (c === 10){ P.push(v, 0, 0); last = P.length - 3; } else if (c === 20 && last !== null) P[last + 1] = v; else if (c === 42 && last !== null) P[last + 2] = v; }
          const closed = (+g[70] & 1) === 1; P.closedBulge = closed; let Q = bulgePts(P); if (closed && Q.length > 2) Q = Q.concat([Q[0], Q[1]]); W = push(L, Mo, Q, closed); break; }
        case "POLYLINE": { if (+g[70] & (16 | 64)) break; const P = e.vs || [], closed = (+g[70] & 1) === 1; P.closedBulge = closed; let Q = bulgePts(P); if (closed && Q.length > 2) Q = Q.concat([Q[0], Q[1]]); W = push(L, Mo, Q, closed); break; }
        case "ARC": W = push(L, Mo, arcPts(+g[10], +g[20], +g[40], +g[50] || 0, +g[51] || 0)); break;
        case "CIRCLE": W = push(L, Mo, arcPts(+g[10], +g[20], +g[40], 0, 360), true); break;
        case "ELLIPSE": { const cx = +g[10], cy = +g[20], mx = +g[11], my = +g[21], ra = +g[40] || 1, t0 = +g[41] || 0, t1 = (g[42] !== undefined ? +g[42] : Math.PI * 2), a = Math.hypot(mx, my), rot = Math.atan2(my, mx), P = []; let e1 = t1; while (e1 <= t0) e1 += Math.PI * 2; const n = 24;
          for (let k = 0; k <= n; k++){ const t = t0 + (e1 - t0) * k / n, x = a * Math.cos(t), y = a * ra * Math.sin(t); P.push(cx + x * Math.cos(rot) - y * Math.sin(rot), cy + x * Math.sin(rot) + y * Math.cos(rot)); } W = push(L, Mo, P); break; }
        case "SPLINE": { const P = []; let c10 = [], c11 = []; for (let k = 0; k < e.p.length; k += 2){ const c = +e.p[k], v = +e.p[k + 1]; if (c === 10) c10.push(v, 0); else if (c === 20 && c10.length) c10[c10.length - 1] = v; else if (c === 11) c11.push(v, 0); else if (c === 21 && c11.length) c11[c11.length - 1] = v; } W = push(L, M, c11.length >= 4 ? c11 : c10); break; }
        case "SOLID": case "TRACE": W = push(L, Mo, [+g[10], +g[20], +g[11], +g[21], +g[13] || +g[12], +g[23] || +g[22], +g[12], +g[22], +g[10], +g[20]], true); break;
        case "TEXT": case "ATTDEF": case "MTEXT": {
          if (e.t === "ATTDEF") break;
          let s = e.t === "MTEXT" ? mtext(e.p.filter((_, k) => k % 2 === 1 && e.p[k - 1] === "3").join("") + (g[1] || "")) : uni(g[1] || "").trim();
          if (!s) break; const aligned = e.t === "TEXT" && (+g[72] || +g[73]) && g[11] !== undefined;
          const q = ap(e.t === "MTEXT" ? M : Mo, aligned ? +g[11] : +g[10], aligned ? +g[21] : +g[20]), sc = Math.hypot(M[0], M[1]);
          // centre of the written text (the insertion point is a corner or the baseline, depending on alignment)
          const h0 = (+g[40] || 1) * sc, Ls = s.split("\n"), tw = Math.max(...Ls.map(x => x.length)) * h0 * .62, th = Ls.length * h0 * 1.35;
          let ax = 0, ay = 0; if (e.t === "MTEXT"){ const at = +g[71] || 1, c = (at - 1) % 3, r = Math.floor((at - 1) / 3); ax = c === 0 ? tw / 2 : c === 1 ? 0 : -tw / 2; ay = r === 0 ? -th / 2 : r === 1 ? 0 : th / 2; }
          else { const hz = +g[72] || 0, vt = +g[73] || 0; ax = hz === 0 ? tw / 2 : hz === 2 ? -tw / 2 : 0; ay = vt === 3 ? -h0 / 2 : vt === 2 ? 0 : h0 / 2; }
          const rot = e.t === "MTEXT" && g[11] !== undefined ? Math.atan2(+g[21], +g[11]) + Math.atan2(M[1], M[0]) : ((+g[50] || 0) * D2R + Math.atan2(M[1], M[0]));
          const cx = q[0] + ax * Math.cos(rot) - ay * Math.sin(rot), cy = q[1] + ax * Math.sin(rot) + ay * Math.cos(rot);
          texts.push({L, s, x:cx, y:cy, x0:q[0], y0:q[1], h:h0, mt:e.t === "MTEXT", at:+g[71] || 0, hid, g:TOP, rot}); if (hid) HN[L] = 1; else VN[L] = 1; if (box) box.push(q[0], q[1]); break; }
        case "INSERT": {
          const B = doc.blocks[g[2]]; if (!B || depth > 14 || (B.flags & 4 && !B.ents.length)) break;
          const sx = g[41] !== undefined ? +g[41] : 1, sy = g[42] !== undefined ? +g[42] : 1, rot = (+g[50] || 0) * D2R, cols = Math.max(1, +g[70] || 1), rows = Math.max(1, +g[71] || 1), dc = +g[44] || 0, dr = +g[45] || 0;
          for (let rI = 0; rI < rows; rI++) for (let cI = 0; cI < cols; cI++){
            const ox = cI * dc, oy = rI * dr, x = +g[10] + ox * Math.cos(rot) - oy * Math.sin(rot), y = +g[20] + ox * Math.sin(rot) + oy * Math.cos(rot);
            const T = [Math.cos(rot) * sx, Math.sin(rot) * sx, -Math.sin(rot) * sy, Math.cos(rot) * sy, x, y], Mb = mul(Mo, mul(T, [1, 0, 0, 1, -B.base[0], -B.base[1]]));
            const ref = {L, name:normLayer(g[2]), raw:g[2], depth, pts:[]}, s0 = segs.length;
            const h0 = hid, rid = RID++; ref.id = rid; CH.push(rid); walk(B.ents, Mb, L, depth + 1, ref.pts, h0); CH.pop(); hid = h0;
            for (let k = s0; k < segs.length; k++){ const P = segs[k].p; for (let j = 0; j < P.length; j += 2) ref.pts.push(P[j], P[j + 1]); }
            const c = ap(Mb, B.base[0], B.base[1]); ref.x = c[0]; ref.y = c[1]; ref.rot = Math.atan2(Mb[1], Mb[0]); ref.bb = bbox(ref.pts); delete ref.pts;
            if (ref.bb) refs.push(ref);
            if (box && ref.bb) box.push(ref.bb[0], ref.bb[1], ref.bb[2], ref.bb[3]);
          }
          break; }
      }
      if (W && box) for (let k = 0; k < W.length; k++) box.push(W[k]);
    }
  }
  walk(doc.ents, ID, null, 0, null, false);
  // layer legends: a short straight sample line with the layer's description written right after it, on the same layer
  const TB = new Map(); texts.forEach(t => { (TB.get(t.L) || TB.set(t.L, []).get(t.L)).push(t); });
  const legT = new Set(), segs2 = segs.filter(s => { if (s.p.length !== 4 || Math.abs(s.p[1] - s.p[3]) > 1e-6) return true; const T = TB.get(s.L); if (!T) return true;
    const x2 = Math.max(s.p[0], s.p[2]), len = Math.abs(s.p[2] - s.p[0]), t = T.find(t => Math.abs(t.y - s.p[1]) < t.h * 2 && t.x >= x2 - t.h && t.x <= x2 + Math.max(len, t.h * 30) && t.s.length > 3);
    if (!t) return true; legT.add(t); return false; });
  const texts2 = texts.filter(t => !legT.has(t));
  return {segs:segs2, texts:texts2, refs, hidden:Object.keys(HN).filter(L => !VN[L]), legends:legT.size, truncated:pts > LIM};
}
function bbox(P){ if (!P || P.length < 2) return null; let a = Infinity, b = Infinity, c = -Infinity, d = -Infinity; for (let k = 0; k < P.length; k += 2){ const x = P[k], y = P[k + 1]; if (!isFinite(x) || !isFinite(y)) continue; if (x < a) a = x; if (x > c) c = x; if (y < b) b = y; if (y > d) d = y; } return a === Infinity ? null : [a, b, c, d]; }

/* ---------- what is what ---------- */
// role of a layer from its name (works with AIA/Uniclass/BS 1192 names and Turkish / Azerbaijani / Russian names)
const ROLE_RX = [
  ["ignore", /dim|ölçü|olcu|razmer|hatch|tarama|grid|aks|axis|tblock|title|antet|vport|viewport|revcld|revision|legend|lejant|defpoints|demo|txt.?snt|leader|^0-txt|setout|conlin|fin.?ceil|ceil|rcp|lite|light|aydınlat|aydinlat|luminaire|elec|elek|cable|kablo|duct|vent|heating|cooling|drain|plumb|sihhi|tesisat|mech|^e-|^m-|^p-|fire|sprink|beam|kiriş|kiris|abv|above|over|found|pile|excav|shad/i],
  ["window", /win|pencere|pəncərə|pencere|okno|окн|glaz|glz|fenetre|fenster|louv|vitr/i],
  ["door", /door|kapı|kapi|qapı|qapi|dver|двер|porte|tür\b|tuer/i],
  ["wallExt", /wall.?ext|ext.?wall|dış.?duvar|dis.?duvar|xarici.?divar|curtain|cur(tain)?wall|wall.?cav|wall.?glz|perde|beton|concrete|A-WALL-EXT|wallstruc|wall.?str|ret.?wall/i],
  ["wall", /wall|duvar|divar|stena|стен|\bmur\b|A-WALL|bölme|bolme|partition/i],
  ["column", /column|kolon|sütun|sutun|колон|pillar|pier/i],
  ["stair", /stair|merdiven|nərdivan|nerdivan|лестн|ramp|rampa|lift|elev|asansör|asansor/i],
  ["area", /nia|niapl|gia|area|alan|space|zone|zona|mahal.?sınır|room.?(poly|bound)|otaq.?sərhəd/i],
  ["roomName", /rm.?name|room.?name|roomname|rm.?no|room.?(no|num|tag)|mahal|oda|otaq|room|space.?name|A-AREA-IDEN|помещ/i],
  ["site", /site|parsel|plot|boundary|sınır|sinir|sərhəd|serhed|property|land|lscape|peyzaj|bahçe|bahce|garden|bağ|hasar|fence|çit|cit|road|yol|pool|havuz|hscape|street|yard|həyət|heyet|terrace|teras|balcon|balkon|A9\d\d/i],
  ["furn", /furn|mobil|mebel|fitt|sanit|kitch|mutfak|banyo|wc|vitrifiye|armatur|equip/i],
];
function roleOf(name){ const n = String(name); for (const [r, rx] of ROLE_RX){ if (rx.test(n)){ if (r === "ignore" && /wall|duvar|divar|door|kap|win|pencere/i.test(n) && !/fitt|lite|light|tag|txt|text|dim|hatch|abv|demo|ceil|beam|elec|aydın|aydin/i.test(n)) continue; return r; } } return "other"; }
// network-related outlets drawn as blocks (Turkish electrical drawings: DATA PRİZİ, TV PRİZİ, TELEFON PRİZİ …)
const KIND_RX = [["outlet", /data|rj.?45|cat.?[5-7]|network|ağ.?pr|ag.?pr|lan\b|f-?o-?pr|fiber|fo.?pr|optik/i], ["tv", /\btv\b|tv.?pr|televiz|anten|sat/i], ["phone", /telefon|phone|tel.?pr|\btel\b/i],
  ["ap", /\bap\b|access.?point|wifi|wi-fi|wlan|kablosuz/i], ["camera", /camera|kamera|cctv|ip.?cam/i], ["access", /kart|card.?read|access|geçiş|gecis|turnike/i], ["intercom", /interkom|intercom|diafon|görüntülü|goruntulu|zil/i],
  ["sensor", /dedekt|detector|sensor|sensör|duman|smoke/i]];
function kindOf(name){ const n = String(name); if (/^\*|^a\$c|anon/i.test(n)) return ""; for (const [k, rx] of KIND_RX) if (rx.test(n)) return k; return ""; }
const UNITS = {1:["in", .0254], 2:["ft", .3048], 4:["mm", .001], 5:["cm", .01], 6:["m", 1], 14:["dm", .1]};

// layers with counts and guessed roles; units; separate floor plans (groups of walls with empty space between them)
function analyze(doc, flat){
  const lay = {};
  const add = (L, k) => { const o = lay[L] = lay[L] || {name:L, segs:0, texts:0, refs:0, role:roleOf(L)}; o[k]++; };
  flat.segs.forEach(s => add(s.L, "segs")); flat.texts.forEach(s => add(s.L, "texts")); flat.refs.forEach(r => { if (r.depth === 0 || roleOf(r.L) === "door" || roleOf(r.L) === "window") add(r.L, "refs"); });
  // a layer drawn only with texts is a room-name layer only if its name says so
  const H = new Set(flat.hidden || []);
  Object.values(lay).forEach(o => { o.hidden = H.has(o.name); if (o.hidden && !/^(door|window|wall|wallExt)$/.test(o.role)) o.role = "ignore"; });
  Object.values(lay).forEach(o => { if (o.role === "area" && !o.segs) o.role = o.texts ? "roomName" : "other"; if (o.role === "roomName" && !o.texts) o.role = o.segs ? "area" : "other"; });
  // units: header first, else from typical door width
  let u = UNITS[+((doc.header.$INSUNITS || {})[70])] || null;
  const doors = flat.refs.filter(r => roleOf(r.L) === "door" || /door|kap[ıi]|qap/i.test(r.name)).map(r => Math.max(r.bb[2] - r.bb[0], r.bb[3] - r.bb[1])).sort((a, b) => a - b);
  const dw = doors.length ? doors[doors.length >> 1] : 0;
  let guess = null; if (dw){ for (const k of [4, 5, 6, 1]){ const m = dw * UNITS[k][1]; if (m > .5 && m < 2.4){ guess = UNITS[k]; break; } } }
  if (!u || (guess && u !== guess && dw * u[1] > 4 || dw * (u || [0, 1])[1] < .3)) u = guess || u;
  if (!u){ const bb = bbox(flat.segs.filter(s => /wall/.test(lay[s.L].role)).flatMap(s => s.p)); const span = bb ? Math.max(bb[2] - bb[0], bb[3] - bb[1]) : 0; u = span > 3000 ? UNITS[4] : span > 300 ? UNITS[5] : UNITS[6]; }
  const kinds = {}; flat.refs.forEach(r => { const k = kindOf(r.name); if (!k) return; (kinds[r.name] = kinds[r.name] || {name:r.name, n:0, kind:k}).n++; });
  return {layers:Object.values(lay).sort((a, b) => (b.segs + b.texts + b.refs) - (a.segs + a.texts + a.refs)), units:u[0], scale:u[1], blocks:Object.values(kinds).sort((a, b) => b.n - a.n)};
}
// floors: boxes of wall pieces grouped while they touch or lie close (gap < 3 m)
function floors(flat, roles, scale){
  const W = flat.segs.filter(s => roles[s.L] === "wall" || roles[s.L] === "wallExt");
  if (!W.length) return [];
  const gap = 3 / scale, B = W.map(s => bbox(s.p));
  // grid buckets keep this fast on big drawings
  const cell = gap * 4, grid = new Map(), par = B.map((_, i) => i), find = i => { while (par[i] !== i) i = par[i] = par[par[i]]; return i; };
  B.forEach((b, i) => { for (let gx = Math.floor((b[0] - gap) / cell); gx <= Math.floor((b[2] + gap) / cell); gx++) for (let gy = Math.floor((b[1] - gap) / cell); gy <= Math.floor((b[3] + gap) / cell); gy++){ const k = gx + "," + gy; let a = grid.get(k); if (!a) grid.set(k, a = []);
    for (const j of a){ const c = B[j]; if (b[0] - gap <= c[2] && c[0] - gap <= b[2] && b[1] - gap <= c[3] && c[1] - gap <= b[3]){ const x = find(i), y = find(j); if (x !== y) par[x] = y; } } a.push(i); } });
  const G = new Map(); B.forEach((b, i) => { const r = find(i); const g = G.get(r) || {bb:[...b], n:0}; g.bb = [Math.min(g.bb[0], b[0]), Math.min(g.bb[1], b[1]), Math.max(g.bb[2], b[2]), Math.max(g.bb[3], b[3])]; g.n++; G.set(r, g); });
  let L = [...G.values()].filter(g => (g.bb[2] - g.bb[0]) * scale > 2.5 && (g.bb[3] - g.bb[1]) * scale > 2.5);
  const maxN = Math.max(...L.map(g => g.n)); L = L.filter(g => g.n >= Math.max(8, maxN * .08));
  // merge boxes that overlap (same plan drawn twice, e.g. floor plan + ceiling plan on top of each other)
  for (let again = true; again;){ again = false; for (let i = 0; i < L.length; i++) for (let j = i + 1; j < L.length; j++){ const a = L[i].bb, b = L[j].bb; if (a[0] < b[2] && b[0] < a[2] && a[1] < b[3] && b[1] < a[3]){ L[i] = {bb:[Math.min(a[0], b[0]), Math.min(a[1], b[1]), Math.max(a[2], b[2]), Math.max(a[3], b[3])], n:L[i].n + L[j].n}; L.splice(j, 1); again = true; break; } } }
  // names: the nearest title-like text below or above each plan
  const TITLE = /kat|floor|mərtəbə|mertebe|etaj|этаж|plan|zemin|bodrum|çatı|cati|roof|ground|basement|level|seviye|mezzanine|asma|giriş|giris|penthouse|zirzəmi|zirzemi|podval/i;
  L.forEach(g => { const [x0, y0, x1, y1] = g.bb, w = x1 - x0, h = y1 - y0; let best = null, bd = Infinity;
    flat.texts.forEach(t => { if (!TITLE.test(t.s) || t.s.length > 60) return; const inX = t.x > x0 - w * .1 && t.x < x1 + w * .1, dy = t.y < y0 ? y0 - t.y : t.y > y1 ? t.y - y1 : -1; if (!inX || dy < 0 || dy > h * .35) return; const d = dy - t.h * 3; if (d < bd){ bd = d; best = t; } });
    g.title = best ? best.s.split("\n")[0] : ""; });
  // order: left to right, then top to bottom (drawing Y goes up)
  L.sort((a, b) => Math.abs(a.bb[1] - b.bb[1]) > (a.bb[3] - a.bb[1]) * .5 ? b.bb[1] - a.bb[1] : a.bb[0] - b.bb[0]);
  return L;
}
/* ---------- one floor → plan ---------- */
const inBox = (bb, x, y, m = 0) => x >= bb[0] - m && x <= bb[2] + m && y >= bb[1] - m && y <= bb[3] + m;
function polyArea(P){ let a = 0; for (let k = 0; k + 3 < P.length; k += 2) a += P[k] * P[k + 3] - P[k + 2] * P[k + 1]; return a / 2; }
function inPoly(P, x, y){ let c = false; for (let i = 0, j = P.length - 2; i < P.length; j = i, i += 2){ const xi = P[i], yi = P[i + 1], xj = P[j], yj = P[j + 1]; if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c; } return c; }
// centre lines of thick walls: two parallel faces 4 … 60 cm apart become one wall line (one wall = one loss for Wi-Fi)
function centerLines(lines, sc){
  const out = [], used = new Uint8Array(lines.length), minT = .04 / sc, maxT = .6 / sc, minL = .3 / sc;
  const L = lines.map(([x1, y1, x2, y2]) => { const len = Math.hypot(x2 - x1, y2 - y1), ux = (x2 - x1) / len, uy = (y2 - y1) / len; return {x1, y1, x2, y2, len, ux, uy}; }).map((s, i) => Object.assign(s, {i}));
  const cell = maxT * 3, grid = new Map(); L.forEach(s => { if (s.len < minL) return; const k = Math.floor((s.x1 + s.x2) / 2 / cell) + "," + Math.floor((s.y1 + s.y2) / 2 / cell); (grid.get(k) || grid.set(k, []).get(k)).push(s); });
  const near = s => { const R = [], cx = Math.floor((s.x1 + s.x2) / 2 / cell), cy = Math.floor((s.y1 + s.y2) / 2 / cell), span = Math.ceil(s.len / 2 / cell) + 1; for (let gx = cx - span; gx <= cx + span; gx++) for (let gy = cy - span; gy <= cy + span; gy++){ const a = grid.get(gx + "," + gy); if (a) R.push(...a); } return R; };
  L.sort((a, b) => b.len - a.len).forEach(s => { if (s.len < minL || used[s.i]) return;
    let best = null, bt = Infinity;
    for (const o of near(s)){ if (o.i === s.i || used[o.i] || Math.abs(s.ux * o.uy - s.uy * o.ux) > .03) continue;
      const d = Math.abs((o.x1 - s.x1) * -s.uy + (o.y1 - s.y1) * s.ux); if (d < minT || d > maxT) continue;
      const t1 = (o.x1 - s.x1) * s.ux + (o.y1 - s.y1) * s.uy, t2 = (o.x2 - s.x1) * s.ux + (o.y2 - s.y1) * s.uy, a = Math.max(0, Math.min(t1, t2)), b = Math.min(s.len, Math.max(t1, t2));
      if (b - a < Math.min(s.len, o.len) * .5) continue; if (d < bt){ bt = d; best = {o, a, b, d}; } }
    if (!best) return; used[s.i] = 1; used[best.o.i] = 1;
    const nx = -s.uy, ny = s.ux, sg = ((best.o.x1 - s.x1) * nx + (best.o.y1 - s.y1) * ny) > 0 ? 1 : -1, off = sg * best.d / 2;
    out.push({x1:s.x1 + s.ux * best.a + nx * off, y1:s.y1 + s.uy * best.a + ny * off, x2:s.x1 + s.ux * best.b + nx * off, y2:s.y1 + s.uy * best.b + ny * off, t:best.d * sc}); });
  return out;
}
// opts: {bb, roles:{layer:role}, scale, kinds:{blockName:kind}, name}
function build(flat, opts){
  const sc = opts.scale, R = opts.roles, bb = opts.bb, pad = 1 / sc;
  const X0 = bb[0] - pad, Y1 = bb[3] + pad;
  const site = flat.segs.filter(s => R[s.L] === "site"), sb = bbox(site.flatMap(s => { const b = bbox(s.p); return b && inBox([bb[0] - 40 / sc, bb[1] - 40 / sc, bb[2] + 40 / sc, bb[3] + 40 / sc], (b[0] + b[2]) / 2, (b[1] + b[3]) / 2) ? s.p : []; }));
  const BB = sb ? [Math.min(bb[0], sb[0]) - pad, Math.min(bb[1], sb[1]) - pad, Math.max(bb[2], sb[2]) + pad, Math.max(bb[3], sb[3]) + pad] : [bb[0] - pad, bb[1] - pad, bb[2] + pad, bb[3] + pad];
  const wmax = Math.max(BB[2] - BB[0], BB[3] - BB[1]) * sc * 1.5, ox = BB[0], oy = BB[3], tx = x => (x - ox) * sc, ty = y => (oy - y) * sc, wm = (BB[2] - BB[0]) * sc, hm = (BB[3] - BB[1]) * sc;
  const inside = s => { const b = bbox(s.p); return b && b[0] <= BB[2] + pad && b[2] >= BB[0] - pad && b[1] <= BB[3] + pad && b[3] >= BB[1] - pad && (b[2] - b[0]) * sc < wmax && (b[3] - b[1]) * sc < wmax; };
  const S = flat.segs.filter(s => R[s.L] && R[s.L] !== "ignore" && R[s.L] !== "other" && inside(s));
  const path = P => { let d = ""; for (let k = 0; k < P.length; k += 2) d += (k ? "L" : "M") + tx(P[k]).toFixed(2) + " " + ty(P[k + 1]).toFixed(2); return d; };
  const by = (r, closed) => S.filter(s => R[s.L] === r && (closed === undefined || !!s.c === closed)).map(s => path(s.p) + (s.c ? "Z" : "")).join("");
  // doors and windows as block references: their box, drawn over the wall gap
  const refs = flat.refs.filter(r => (R[r.L] === "door" || R[r.L] === "window") && inBox(BB, (r.bb[0] + r.bb[2]) / 2, (r.bb[1] + r.bb[3]) / 2));
  const top = refs.filter(r => !refs.some(o => o !== r && o.depth < r.depth && o.bb[0] <= r.bb[0] && o.bb[1] <= r.bb[1] && o.bb[2] >= r.bb[2] && o.bb[3] >= r.bb[3] && R[o.L] === R[r.L]));
  // SVG drawing in metres × 20 px (sharp at any zoom), colours by role
  const k = 20, vb = `0 0 ${(wm * k).toFixed(1)} ${(hm * k).toFixed(1)}`, sw = v => (v / k).toFixed(3);
  const gS = (r, st, closed) => { const d = by(r, closed); return d ? `<path d="${d}" ${st}/>` : ""; };
  const openings = top.map(r => { const w = (r.bb[2] - r.bb[0]) * sc, h = (r.bb[3] - r.bb[1]) * sc, horiz = w >= h, door = R[r.L] === "door";
    const x = tx(r.bb[0]), y = ty(r.bb[3]); return door ? `<rect x="${x.toFixed(2)}" y="${y.toFixed(2)}" width="${w.toFixed(2)}" height="${h.toFixed(2)}" fill="#f5e6d3" fill-opacity=".55" stroke="none"/>`
      : `<rect x="${(horiz ? x : x + w / 2 - .07).toFixed(2)}" y="${(horiz ? y + h / 2 - .07 : y).toFixed(2)}" width="${(horiz ? w : .14).toFixed(2)}" height="${(horiz ? .14 : h).toFixed(2)}" fill="#cfe6ff" stroke="#2b7bd0" stroke-width=".035"/>`; }).join("");
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${wm.toFixed(2)} ${hm.toFixed(2)}" width="${(wm * k).toFixed(0)}" height="${(hm * k).toFixed(0)}" fill="none" stroke-linecap="round" stroke-linejoin="round">
<rect width="100%" height="100%" fill="#fff"/>
${gS("site", 'stroke="#2e9d57" stroke-width=".06" stroke-dasharray=".5 .25"')}
${gS("furn", 'stroke="#b9bfca" stroke-width=".02"')}
${gS("stair", 'stroke="#59607a" stroke-width=".03"')}
${openings}
${gS("column", 'stroke="#1d2433" stroke-width=".04" fill="#59607a"')}
${gS("wall", 'stroke="#2b3240" stroke-width=".04" fill="#6b7385" fill-rule="nonzero"', true)}
${gS("wall", 'stroke="#2b3240" stroke-width=".045"', false)}
${gS("wallExt", 'stroke="#111722" stroke-width=".05" fill="#3b4354" fill-rule="nonzero"', true)}
${gS("wallExt", 'stroke="#111722" stroke-width=".07"', false)}
${gS("window", 'stroke="#2b7bd0" stroke-width=".045"')}
${gS("door", 'stroke="#a8641f" stroke-width=".04"')}
</svg>`;
  void vb; void sw;
  // rooms: closed area outlines (best), else a box around each room name bounded by the nearest walls
  // the same name written twice close together (architect's copy + engineer's copy) counts once; floor titles are not rooms
  const FT = /^(bodrum|zemin|giriş|giris|çatı|cati|asma|zirzəmi|zirzemi|podval|ground|basement|roof|mezzanine|\d+\s*[.-]?\s*(kat|mərtəbə|mertebe|floor|etaj))(\s*(kat|kat[ıi]|floor|mərtəbə|mertebe))?(\s*plan[ıi]?)?$/i;
  const names = [], ftitles = [];
  flat.texts.filter(t => R[t.L] === "roomName" && inBox(bb, t.x, t.y) && t.s.length <= 60 && /\p{L}/u.test(t.s)).sort((a, b) => (a.hid ? 1 : 0) - (b.hid ? 1 : 0)).forEach(t => {
    const nm = t.s.split("\n")[0].trim(); if (FT.test(nm.toLocaleLowerCase("tr"))){ ftitles.push(nm); return; }
    if (names.some(o => o.s.split("\n")[0].trim().toLowerCase() === nm.toLowerCase() && Math.hypot(o.x - t.x, o.y - t.y) * sc < 2.5)) return; names.push(t); });
  const fa = (bb[2] - bb[0]) * (bb[3] - bb[1]) * sc * sc, seenP = [];
  const polys = S.filter(s => R[s.L] === "area" && s.c && s.p.length >= 8).map(s => ({p:s.p, a:Math.abs(polyArea(s.p)) * sc * sc, b:bbox(s.p)})).filter(o => o.a > 1.2 && o.a < fa * .3)
    .filter(o => { if (seenP.some(q => Math.abs(q.b[0] - o.b[0]) + Math.abs(q.b[1] - o.b[1]) + Math.abs(q.b[2] - o.b[2]) + Math.abs(q.b[3] - o.b[3]) < .05 / sc)) return false; seenP.push(o); return true; }).sort((a, b) => a.a - b.a);
  const rooms = [];
  const cleanName = s => s.split("\n").map(x => x.trim()).filter(x => x && !/^[\d.,\s]+\s*(m2|m²|㎡)?$/i.test(x) && !/^(\+|-)?\d+[.,]\d+$/.test(x))[0] || "";
  const N = names.map(t => ({t, nm:cleanName(t.s)})).filter(o => o.nm);
  // each area outline goes to the room name inside it; two names in one outline → the one nearest its middle keeps it
  N.forEach(o => { o.P = polys.find(P => inPoly(P.p, o.t.x, o.t.y)) || null; });
  polys.forEach(P => { const inside = N.filter(o => o.P === P); if (inside.length < 2) return; const c = [(P.b[0] + P.b[2]) / 2, (P.b[1] + P.b[3]) / 2]; inside.sort((a, b) => Math.hypot(a.t.x - c[0], a.t.y - c[1]) - Math.hypot(b.t.x - c[0], b.t.y - c[1])).slice(1).forEach(o => { o.P = null; }); });
  const WL = S.filter(s => R[s.L] === "wall" || R[s.L] === "wallExt" || R[s.L] === "door" || R[s.L] === "window");
  const hit = (t, dx, dy) => { let best = 12 / sc; WL.forEach(s => { const P2 = s.p; for (let i = 0; i + 3 < P2.length; i += 2){ const ax = P2[i], ay = P2[i + 1], ex = P2[i + 2] - ax, ey = P2[i + 3] - ay, den = dx * ey - dy * ex; if (Math.abs(den) < 1e-12) continue; const u = ((ax - t.x) * ey - (ay - t.y) * ex) / den, v = ((ax - t.x) * dy - (ay - t.y) * dx) / den; if (u > .05 / sc && v >= 0 && v <= 1 && u < best) best = u; } }); return best; };
  N.forEach(({t, nm, P}) => {
    let g, poly = null;
    if (P){ const b = P.b; g = {x:tx(b[0]), y:ty(b[3]), w:(b[2] - b[0]) * sc, h:(b[3] - b[1]) * sc}; poly = []; for (let i = 0; i + 1 < P.p.length - 2; i += 2) poly.push(+tx(P.p[i]).toFixed(2), +ty(P.p[i + 1]).toFixed(2)); }
    else { let l = hit(t, -1, 0), r = hit(t, 1, 0), u = hit(t, 0, 1), d = hit(t, 0, -1); const m = 1 / sc;
      if (l + r < 2 * m){ l = Math.max(l, m); r = Math.max(r, m); } if (u + d < 2 * m){ u = Math.max(u, m); d = Math.max(d, m); } g = {x:tx(t.x - l), y:ty(t.y + u), w:(l + r) * sc, h:(u + d) * sc}; }
    const rnd = v => Math.round(v * 10) / 10;
    rooms.push({name:nm, geo:{x:rnd(g.x), y:rnd(g.y), w:Math.max(.5, rnd(g.w)), h:Math.max(.5, rnd(g.h)), poly, lx:rnd(tx(t.x) - g.x), ly:rnd(ty(t.y) - g.y)}, area:P ? Math.round(P.a * 10) / 10 : Math.round(g.w * g.h * 10) / 10, exact:!!P}); });
  // Wi-Fi walls: wall centre lines + every door / window as its own piece that closes the gap
  const lines = []; S.filter(s => R[s.L] === "wall" || R[s.L] === "wallExt").forEach(s => { for (let i = 0; i + 3 < s.p.length; i += 2) lines.push([s.p[i], s.p[i + 1], s.p[i + 2], s.p[i + 3], R[s.L]]); });
  const ext = new Set(); const CL = centerLines(lines.map(l => l.slice(0, 4)), sc);
  const walls = CL.filter(w => Math.hypot(w.x2 - w.x1, w.y2 - w.y1) * sc >= .3).map(w => ({x1:tx(w.x1), y1:ty(w.y1), x2:tx(w.x2), y2:ty(w.y2), kind:"wall", mat:w.t >= .25 ? "concrete" : w.t >= .14 ? "brick" : "drywall"}));
  void ext;
  top.forEach(r => { const w = (r.bb[2] - r.bb[0]) * sc, h = (r.bb[3] - r.bb[1]) * sc, horiz = w >= h, cx = tx((r.bb[0] + r.bb[2]) / 2), cy = ty((r.bb[1] + r.bb[3]) / 2), door = R[r.L] === "door";
    const len = door ? Math.min(Math.max(w, h), 2.6) : Math.max(w, h); if (len < .3 || len > 8) return;
    walls.push(horiz ? {x1:cx - len / 2, y1:cy, x2:cx + len / 2, y2:cy, kind:door ? "door" : "window", mat:door ? "door" : "glass"} : {x1:cx, y1:cy - len / 2, x2:cx, y2:cy + len / 2, kind:door ? "door" : "window", mat:door ? "door" : "glass"}); });
  walls.forEach(w => { ["x1", "y1", "x2", "y2"].forEach(k2 => { w[k2] = Math.round(w[k2] * 100) / 100; }); });
  // network outlets drawn as blocks
  const outlets = flat.refs.filter(r => opts.kinds && opts.kinds[r.name] && inBox(BB, r.x, r.y)).map(r => ({kind:opts.kinds[r.name], block:r.name, x:Math.round(tx(r.x) * 10) / 10, y:Math.round(ty(r.y) * 10) / 10}));
  // no floor title: the floor part shared by room names ("1 KAT HOLÜ", "1 KAT BALKON" → "1 KAT")
  if (!ftitles.length){ const C = {}; rooms.forEach(r => { const m = r.name.match(/^(.{1,14}?\s(kat|katı|mərtəbə|mertebe|floor|etaj|этаж))\b/i); if (m) C[m[1]] = (C[m[1]] || 0) + 1; }); const best = Object.entries(C).sort((a, b) => b[1] - a[1])[0]; if (best && best[1] >= 2) ftitles.push(best[0]); }
  // the same room found twice (a second copy of its name outside the outline → an estimated box over the real room): dropped
  const nk = s => s.toLocaleLowerCase("tr").replace(/\s*\d+$/, "").trim(), ov = (a, b) => { const x = Math.max(0, Math.min(a.x + a.w, b.x + b.w) - Math.max(a.x, b.x)), y = Math.max(0, Math.min(a.y + a.h, b.y + b.h) - Math.max(a.y, b.y)); return x * y / Math.max(.01, Math.min(a.w * a.h, b.w * b.h)); };
  for (let i = rooms.length - 1; i >= 0; i--){ const r = rooms[i]; if (r.exact) continue; const tw = rooms.find(o => o !== r && nk(o.name) === nk(r.name) && ov(o.geo, r.geo) > .5); if (tw) rooms.splice(i, 1); }
  // editable drawing: every wall line of a room (with its doors and windows) as one piece of that room; furniture, stairs,
  // columns and the yard in pieces of what touches; closed yard outlines as boundaries the user can reshape point by point
  const pieces = opts.pieces === false ? null : piecesOf(S, rooms, tx, ty, sc, R, objKey(flat, sc, 6));
  // other writing on the plan (notes, equipment names, levels written as words): labels of their own; room names, numbers
  // alone and codes are left out
  const rn = new Set(rooms.map(r => r.name.toLocaleUpperCase("tr"))), labels = [];
  flat.texts.forEach(t => { const r = R[t.L] || "other"; if (r === "roomName" || (r === "ignore" && !/yazı|yazi|text|note|label|^not\b/i.test(t.L)) || !inBox(BB, t.x, t.y)) return;
    const s2 = String(t.s || "").replace(/\s+/g, " ").trim(); if (s2.length < 3 || s2.length > 80 || /^[\d\s.,:;+\-x×/%°'"()=±]+$/.test(s2) || /^[a-z]{1,3}\.[a-z]{1,3}/i.test(s2) || MEAS.test(s2) || rn.has(s2.toLocaleUpperCase("tr"))) return;
    labels.push({x:Math.round(tx(t.x) * 100) / 100, y:Math.round(ty(t.y) * 100) / 100, text:s2, h:t.h * sc, rot:t.rot ? Math.round(-t.rot / D2R) : 0}); });
  return {svg, title:ftitles[0] || "", pieces, labels, origin:[ox, oy], wm:Math.round(wm * 10) / 10, hm:Math.round(hm * 10) / 10, rooms, walls, outlets, doors:top.filter(r => R[r.L] === "door").length, windows:top.filter(r => R[r.L] === "window").length, site:!!sb};
}
function piecesOf(S, rooms, tx, ty, sc, R, OK){
  const rr = v => Math.round(v * 100) / 100, M = s => { const o = new Array(s.p.length); for (let k = 0; k < s.p.length; k += 2){ o[k] = tx(s.p[k]); o[k + 1] = ty(s.p[k + 1]); } return o; };
  const bbM = P => bbox(P), WALLR = {wall:1, wallExt:1, door:1, window:1};
  // units: {r:role, P:[x,y…] metres, c:closed}
  const units = []; S.forEach(s => { const r = R[s.L]; if (!r || r === "area") return; const P = M(s), b = bbM(P); if (!b) return;
    if (WALLR[r] && P.length > 4 && !(s.c && Math.max(b[2] - b[0], b[3] - b[1]) < 2.5)){ for (let k = 0; k + 3 < P.length; k += 2) units.push({r, P:[P[k], P[k + 1], P[k + 2], P[k + 3]], c:false}); }
    else units.push({r, P, c:!!s.c, g:OK(s)}); });
  units.forEach(u => { u.b = bbM(u.P); u.cx = (u.b[0] + u.b[2]) / 2; u.cy = (u.b[1] + u.b[3]) / 2; });
  const roomOf = u => { let best = -1, ba = Infinity; rooms.forEach((rm, i) => { const g = rm.geo, m = .35; if (u.cx < g.x - m || u.cx > g.x + g.w + m || u.cy < g.y - m || u.cy > g.y + g.h + m) return; const a = g.w * g.h; if (a < ba){ ba = a; best = i; } }); return best; };
  const out = [], boundaries = [];
  const mk = (k, list, extra) => { const B = bbox(list.flatMap(u => [u.b[0], u.b[1], u.b[2], u.b[3]])); if (!B) return; const x0 = B[0], y0 = B[1], w = Math.max(.05, B[2] - B[0]), h = Math.max(.05, B[3] - B[1]);
    const by = {}; list.forEach(u => { const key = u.r + (u.c && (u.r === "column" || u.r === "wall" || u.r === "wallExt") ? ":f" : ""); let d = ""; for (let k2 = 0; k2 < u.P.length; k2 += 2) d += (k2 ? "L" : "M") + rr(u.P[k2] - x0) + " " + rr(u.P[k2 + 1] - y0); by[key] = (by[key] || "") + d + (u.c ? "Z" : ""); });
    out.push(Object.assign({k, x:rr(x0), y:rr(y0), w:rr(w), h:rr(h), w0:rr(w), h0:rr(h), rot:0, p:Object.entries(by)}, extra || {})); };
  // walls, doors, windows → by room
  const byRoom = new Map(), loose = [];
  units.filter(u => WALLR[u.r]).forEach(u => { const i = roomOf(u); if (i < 0) loose.push(u); else (byRoom.get(i) || byRoom.set(i, []).get(i)).push(u); });
  byRoom.forEach((L, i) => mk("rwall", L, {room:i}));
  // the rest: groups of pieces that touch each other (gap 3 cm), split by role
  const groups = (L, gap) => { const par = L.map((_, i) => i), find = i => { while (par[i] !== i) i = par[i] = par[par[i]]; return i; }, cell = 1, grid = new Map();
    L.forEach((u, i) => { const b = u.b; for (let gx = Math.floor((b[0] - gap) / cell); gx <= Math.floor((b[2] + gap) / cell); gx++) for (let gy = Math.floor((b[1] - gap) / cell); gy <= Math.floor((b[3] + gap) / cell); gy++){ const key = gx + "," + gy; let a = grid.get(key); if (!a) grid.set(key, a = []);
      for (const j of a){ const c = L[j].b; if (b[0] - gap <= c[2] && c[0] - gap <= b[2] && b[1] - gap <= c[3] && c[1] - gap <= b[3]){ const x = find(i), y = find(j); if (x !== y) par[x] = y; } } a.push(i); } });
    const G = new Map(); L.forEach((u, i) => { const r = find(i); (G.get(r) || G.set(r, []).get(r)).push(u); }); return [...G.values()]; };
  groups(loose, .05).forEach(L => mk("wall", L));
  // furniture and fittings: every block (a bed, a WC, a sink) is a piece of its own; loose lines join what they touch
  { const byG = new Map(); units.filter(u => u.r === "furn" && u.g >= 0).forEach(u => (byG.get(u.g) || byG.set(u.g, []).get(u.g)).push(u)); byG.forEach(L => mk("furn", L)); }
  ["furn", "stair", "column", "other"].forEach(r => groups(units.filter(u => u.r === r && !(r === "furn" && u.g >= 0)), .03).forEach(L => { const B = bbox(L.flatMap(u => u.b)); if (B && Math.max(B[2] - B[0], B[3] - B[1]) > 12) L.forEach(u => mk(r, [u])); else mk(r, L); }));
  units.filter(u => u.r === "site").forEach(u => { if (u.c && u.P.length >= 8 && u.P.length <= 800){ const P = u.P.slice(0, -2).map(rr); boundaries.push(P); } else mk("site", [u]); });
  return {shapes:out, boundaries};
}
/* ---------- landscape (site plan) drawings ---------- */
// role of a layer in a landscape / site drawing: what a piece is drawn as on the site plan (none of them block a camera)
const LROLE_RX = [
  ["ignore", /dim|ölçü|olcu|razmer|hatch|tarama|grid|axis|tblock|title|antet|vport|viewport|revcld|revision|defpoints|leader|lejant|legend|setout|conlin|drno|dynamic blocks|^0-txt|_text$|^text$|2-sps|elv|bemass|kot|level.?mark/i],
  ["wall", /A041E|build.?out|bina.?kontur|wall.?ext|ext.?wall|dış.?duvar|dis.?duvar|xarici.?divar|exterior.?wall|A210G/i],
  ["plant", /ntr|bitki|plant|tree|ağac|agac|ağaç|agaç|shrub|bush|\bkol\b|çalı|cali|çim|grass|lawn|veg|flora|hedge|çit.?bitki|palm/i],
  ["light", /lite|light|aydın|aydin|bollard|lamp|luminaire|lighting|işıq|isiq|armatür.?ayd/i],
  ["water", /pool|havuz|hovuz|water|fountain|şelale|selale|şəlalə|gölet|golet|pond/i],
  ["road", /road|\byol\b|street|asfalt|asphalt|A950/i],
  ["edge", /site.?ex|parsel|plot|boundary|sınır|sinir|sərhəd|serhed|property|A910/i],
  ["curb", /curb|kerb|bordür|bordur|ADET_0/i],
  ["pave", /pave|döşe|dose|tile|karo|kaplama|deck|ahşap|ahsap|wood|stone|taş|tas\b|ADET/i],
  ["stair", /stair|merdiven|nərdivan|nerdivan|ramp|step|basamak/i],
  ["furn", /furn|mobil|mebel|fitt|sanit|equip|seat|bench|oturma|şezlong|sezlong|lounger|umbrella|şemsiye|semsiye/i],
  ["hard", /wall|duvar|divar|column|kolon|sütun|sutun|build|bina|outline|footprint|A2\d\d|A0\d\d|secur|fence|hasar|\bçit\b|\bcit\b|pergola|pergole|canopy|roof|çatı|cati/i],
];
function lroleOf(name){ const n = String(name); for (const [r, rx] of LROLE_RX) if (rx.test(n)) return r; return "other"; }
// Douglas–Peucker simplification of [x,y …]
function simp(P, tol){ const n = P.length / 2; if (n <= 2) return P; const keep = new Uint8Array(n); keep[0] = keep[n - 1] = 1; const st = [[0, n - 1]];
  while (st.length){ const [a, b] = st.pop(); const ax = P[a * 2], ay = P[a * 2 + 1], dx = P[b * 2] - ax, dy = P[b * 2 + 1] - ay, L = Math.hypot(dx, dy); let im = -1, dm = tol;
    for (let i = a + 1; i < b; i++){ const px = P[i * 2] - ax, py = P[i * 2 + 1] - ay, d = L > 1e-9 ? Math.abs(px * dy - py * dx) / L : Math.hypot(px, py); if (d > dm){ dm = d; im = i; } }
    if (im > 0){ keep[im] = 1; st.push([a, im], [im, b]); } }
  const o = []; for (let i = 0; i < n; i++) if (keep[i]) o.push(P[i * 2], P[i * 2 + 1]); return o; }
// heights and levels written as notes ("FL:260 cm", "H:70", "+3.20"): not labels
const MEAS = /^[\p{L}]{0,4}\s*[:=]?\s*[+\-±]?[\d.,]+\s*(cm|mm|m|sm)?$/iu;
const inPolyF = (H, x, y) => { let c = false; for (let i = 0, j = H.length - 2; i < H.length; j = i, i += 2){ const xi = H[i], yi = H[i + 1], xj = H[j], yj = H[j + 1]; if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c; } return c; };
/* Where the drawing sits on the site plan: the building outline drawn in the landscape file is matched against the
   building walls already on the site plan. Candidates are closed outlines of about the right size; each is tried with its
   corners on the corners of the walls' box and scored by how many of its points lie on a wall (within 25 cm).
   target: {bb:[x0,y0,x1,y1] in metres, near(x, y) → distance to the closest wall}. Returns {M, poly, score, L} or null. */
function siteFit(flat, scale, target){
  if (!target || !target.bb) return null; const [t0, u0, t1, u1] = target.bb, TW = t1 - t0, TH = u1 - u0; let best = null;
  const C = flat.segs.filter(s => { if (!s.c || s.p.length < 10) return false; const b = bbox(s.p); if (!b) return false; const w = (b[2] - b[0]) * scale, h = (b[3] - b[1]) * scale;
    return w >= 4 && h >= 4 && w <= TW * 1.15 + 1 && h <= TH * 1.15 + 1 && w >= TW * .4 && h >= TH * .4; });
  // outlines named as the building first; at most 40 tried
  const named = L => /build|bina|outline|footprint|A041|kontur|ayak|bldg|house/i.test(L);
  C.sort((a, b) => named(b.L) - named(a.L) || b.p.length - a.p.length).slice(0, 40).forEach(s => { const b = bbox(s.p), w = (b[2] - b[0]) * scale, h = (b[3] - b[1]) * scale;
    // points along the outline every 50 cm (corners alone give a few long walls too little say)
    const V = []; for (let k = 0; k + 1 < s.p.length; k += 2){ const x = (s.p[k] - b[0]) * scale, y = (b[3] - s.p[k + 1]) * scale; V.push(x, y);
      if (k + 3 < s.p.length){ const x2 = (s.p[k + 2] - b[0]) * scale, y2 = (b[3] - s.p[k + 3]) * scale, n = Math.floor(Math.hypot(x2 - x, y2 - y) / .5); for (let i = 1; i < n; i++) V.push(x + (x2 - x) * i / n, y + (y2 - y) * i / n); } }
    // mean distance of the outline's points to the walls (capped at 80 cm): drawings disagree a little (plaster faces, terraces)
    const cost = (ox, oy) => { let c = 0; for (let a = 0; a < V.length; a += 2) c += Math.min(target.near(ox + V[a], oy + V[a + 1]), .8); return c / (V.length / 2); };
    // every position over the walls' box, 50 cm steps; then the best few to 5 cm
    const G = []; for (let ox = t0 - w * .5; ox <= t1 - w * .5; ox += .5) for (let oy = u0 - h * .5; oy <= u1 - h * .5; oy += .5) G.push([cost(ox, oy), ox, oy]);
    G.sort((a, c) => a[0] - c[0]).slice(0, 6).forEach(([, ox, oy]) => { let bc = cost(ox, oy), bx = ox, by = oy;
      for (let r = .25; r >= .05 - 1e-9; r /= 2) for (let again = true; again;){ again = false; for (const [dx, dy] of [[r, 0], [-r, 0], [0, r], [0, -r]]){ const c = cost(bx + dx, by + dy); if (c < bc - 1e-9){ bc = c; bx += dx; by += dy; again = true; } } }
      let on = 0; for (let a = 0; a < V.length; a += 2) if (target.near(bx + V[a], by + V[a + 1]) < .3) on++;
      // an outline named as the building may disagree more with the walls (it is drawn on its own); any other must lie right on them
      const f = on / (V.length / 2), nm = named(s.L), ok = nm ? bc < .5 && f >= .4 : bc < .2 && f >= .7, score = bc - (nm ? 1 : 0);
      if (ok && (!best || score < best.score)) best = {score, on:f, L:s.L, poly:s.p, ox:bx, oy:by, X0:b[0], Y1:b[3]}; }); });
  if (!best) return null; const {ox, oy, X0, Y1} = best;
  return {M:(X, Y) => [ox + (X - X0) * scale, oy + (Y1 - Y) * scale], poly:best.poly, score:best.on, L:best.L};
}
/* Landscape pieces: every block reference (a tree, a lamp, a bench …) is one piece; loose lines and outlines are joined
   with what they touch on the same role (as in a floor plan). Heavy plant symbols are thinned so a large site stays quick.
   opts: {roles, M(X,Y)→[x,y] metres, clip: outline [X,Y …] whose inside is dropped (the building: drawn by its floors),
   box:[x0,y0,x1,y1] metres kept, skipText(s)}. Returns {shapes:[{k, x, y, w, h, w0, h0, rot, p}], labels:[{x, y, text, h, rot}]}. */
// closed outlines on «building wall» layers: the building parts of the site (house, garage, a pergola …) for the user to confirm
function wallOutlines(flat, roles, scale){ const out = [];
  flat.segs.forEach((s, i) => { if (roles[s.L] !== "wall" || !s.c || s.p.length < 8) return; const b = bbox(s.p); if (!b) return; const w = (b[2] - b[0]) * scale, h = (b[3] - b[1]) * scale; if (w * h < 4) return;
    out.push({i, s, L:s.L, w:Math.round(w * 10) / 10, h:Math.round(h * 10) / 10, cx:(b[0] + b[2]) / 2, cy:(b[1] + b[3]) / 2}); });
  return out; }
function landscape(flat, opts){
  const R = opts.roles, M = opts.M, rr = v => Math.round(v * 100) / 100, box = opts.box;
  // the building: the outline the drawing was matched by, and the building outlines the user kept (their inside is drawn by the
  // floors: only symbols — cars, furniture — are kept there, lines and writing are left out)
  const solids = (opts.solids || []).map(s => s.p).concat(opts.clip ? [opts.clip] : []), solidSeg = new Set(opts.solids || []);
  const inside = (X, Y) => solids.some(P => inPolyF(P, X, Y));
  const units = new Map();   // group key → [{r, P (metres), c}]
  let nk = 0; const OK = objKey(flat, opts.scale || 1, 10);
  flat.segs.forEach(s => { const r = R[s.L] || "other"; if (r === "ignore") return; const P = s.p;
    if (solids.length && !s.ins && !solidSeg.has(s) && !(r === "wall" && s.c)){ let all = true; for (let k = 0; k + 1 < P.length; k += 2) if (!inside(P[k], P[k + 1])){ all = false; break; } if (all) return; }
    const Q = new Array(P.length); let any = !box; for (let k = 0; k + 1 < P.length; k += 2){ const q = M(P[k], P[k + 1]); Q[k] = q[0]; Q[k + 1] = q[1]; if (!any && q[0] >= box[0] && q[0] <= box[2] && q[1] >= box[1] && q[1] <= box[3]) any = true; }
    if (!any) return;
    // a building outline is a piece of its own: a wall that blocks the cameras (or a plain outline, if the user said it is not a building)
    const solid = solidSeg.has(s), rr2 = r === "wall" ? (solid ? "wallExt" : s.c ? "hard" : "wallExt") : r;
    const ok = OK(s), key = solid || (r === "wall" && s.c) ? "s" + (nk++) : ok >= 0 ? "i" + ok : "l" + rr2; if (!units.has(key)) units.set(key, []); units.get(key).push({r:rr2, P:Q, c:s.c, solid}); });
  const shapes = [];
  const mk = list => { let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity; list.forEach(u => { for (let k = 0; k + 1 < u.P.length; k += 2){ const x = u.P[k], y = u.P[k + 1]; if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; } });
    if (x0 === Infinity) return; const dia = Math.max(x1 - x0, y1 - y0, .05), plant = list.some(u => u.r === "plant");
    let L = list.map(u => { let ex = 0; const b = bbox(u.P); if (b) ex = Math.max(b[2] - b[0], b[3] - b[1]); return {u, ex}; });
    if (plant && L.length > 4) L = L.filter(o => o.ex >= dia * .06);
    let parts = L.map(({u}) => ({r:u.r, P:simp(u.P, u.r === "wallExt" || u.r === "hard" ? .005 : Math.max(.01, dia * (plant ? .03 : .005))), c:u.c}));
    if (plant){ const tot = parts.reduce((a, q) => a + q.P.length / 2, 0); if (tot > 160 && parts.length > 8){ parts.sort((a, b) => b.P.length - a.P.length); const k = Math.ceil(tot / 160); parts = parts.filter((_, i) => i % k === 0); } }
    const by = {}; parts.forEach(q => { const key = q.r === "water" && q.c ? "water:f" : q.r; let d = ""; for (let k = 0; k + 1 < q.P.length; k += 2) d += (k ? "L" : "M") + rr(q.P[k] - x0) + " " + rr(q.P[k + 1] - y0); if (q.c) d += "Z"; by[key] = (by[key] || "") + d; });
    const w = Math.max(.05, rr(x1 - x0)), h = Math.max(.05, rr(y1 - y0));
    const o = {k:"lnd", x:rr(x0), y:rr(y0), w, h, w0:w, h0:h, rot:0, p:Object.entries(by)}; if (list.some(u => u.solid)) o.solid = true; shapes.push(o); };
  // loose lines of one role: pieces of what touches (a path edge, a curb run), never one piece across the whole site
  const touch = (L, gap) => { const B = L.map(u => bbox(u.P)), par = L.map((_, i) => i), find = i => { while (par[i] !== i) i = par[i] = par[par[i]]; return i; }, grid = new Map();
    B.forEach((b, i) => { for (let gx = Math.floor((b[0] - gap)); gx <= Math.floor((b[2] + gap)); gx++) for (let gy = Math.floor((b[1] - gap)); gy <= Math.floor((b[3] + gap)); gy++){ const k = gx + "," + gy; let a = grid.get(k); if (!a) grid.set(k, a = []);
      for (const j of a){ const c = B[j]; if (b[0] - gap <= c[2] && c[0] - gap <= b[2] && b[1] - gap <= c[3] && c[1] - gap <= b[3]){ const x = find(i), y = find(j); if (x !== y) par[x] = y; } } a.push(i); } });
    const G = new Map(); L.forEach((u, i) => { const r = find(i); (G.get(r) || G.set(r, []).get(r)).push(u); }); return [...G.values()]; };
  units.forEach((list, key) => { if (key[0] === "i"){
      // a symbol away from the plot (the drawing's legend, the neighbours' trees) is left out
      if (opts.inPlot){ const b = bbox(list.flatMap(u => bbox(u.P))); if (b && !opts.inPlot((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)) return; }
      mk(list); return; }
    touch(list, .03).forEach(g => { const b = bbox(g.flatMap(u => bbox(u.P))); if (b && Math.max(b[2] - b[0], b[3] - b[1]) > 12) g.forEach(u => mk([u])); else mk(g); }); });
  // writing: names of places and notes, each a label of its own (numbers alone, sizes and plant codes are left out)
  const labels = [];
  flat.texts.forEach(t => { if ((R[t.L] || "other") === "ignore" && !/lejant|legend|yazı|yazi|text|txt|not|note|label/i.test(t.L)) return; const s = String(t.s || "").replace(/\s+/g, " ").trim();
    if (s.length < 3 || /^[\d\s.,:;+\-x×/%°'"()=]+$/.test(s) || /^[a-z]{1,3}\.[a-z]{1,3}/i.test(s) || MEAS.test(s) || (opts.skipText && opts.skipText(s))) return;
    if (solids.length && inside(t.x, t.y)) return; const q = M(t.x, t.y); if (box && (q[0] < box[0] || q[0] > box[2] || q[1] < box[1] || q[1] > box[3])) return;
    labels.push({x:rr(q[0]), y:rr(q[1]), text:s, h:t.h * (opts.scale || 1), rot:t.rot ? Math.round(-t.rot / D2R) : 0}); });
  return {shapes, labels};
}
/* One object of the drawing a piece belongs to: the outermost block reference around it that is small enough to be one thing
   (a bed, a tree, a lamp) — a whole floor or site drawn as one block does not make one piece of everything. -1: loose line. */
function objKey(flat, scale, maxM){ const BB = new Map(); flat.refs.forEach(r => { if (r.id !== undefined && r.bb) BB.set(r.id, r.bb); });
  return s => { if (!s.ch) return -1; for (const id of s.ch){ const b = BB.get(id); if (b && Math.max(b[2] - b[0], b[3] - b[1]) * scale <= maxM) return id; } return -1; }; }
/* ---------- floors over each other ---------- */
// distance from a point to the nearest of many lines [[x1,y1,x2,y2] …] (metres), through 1 m cells
function nearOf(S){ const G = new Map(); S.forEach((q, i) => { for (let gx = Math.floor(Math.min(q[0], q[2])); gx <= Math.floor(Math.max(q[0], q[2])); gx++) for (let gy = Math.floor(Math.min(q[1], q[3])); gy <= Math.floor(Math.max(q[1], q[3])); gy++){ const k = gx + "," + gy; (G.get(k) || G.set(k, []).get(k)).push(i); } });
  return (x, y) => { let d = Infinity; for (let gx = Math.floor(x) - 1; gx <= Math.floor(x) + 1; gx++) for (let gy = Math.floor(y) - 1; gy <= Math.floor(y) + 1; gy++){ const a = G.get(gx + "," + gy); if (!a) continue;
    for (const i of a){ const [x1, y1, x2, y2] = S[i], ex = x2 - x1, ey = y2 - y1, L2 = ex * ex + ey * ey || 1e-9, u = Math.max(0, Math.min(1, ((x - x1) * ex + (y - y1) * ey) / L2)); d = Math.min(d, Math.hypot(x - x1 - ex * u, y - y1 - ey * u)); } } return d; }; }
// points every 50 cm along lines (at most ~800, spread evenly)
function sampleOf(S){ const V = []; S.forEach(q => { const n = Math.max(1, Math.floor(Math.hypot(q[2] - q[0], q[3] - q[1]) / .5)); for (let i = 0; i <= n; i++) V.push(q[0] + (q[2] - q[0]) * i / n, q[1] + (q[3] - q[1]) * i / n); });
  if (V.length <= 1600) return V; const k = Math.ceil(V.length / 1600), o = []; for (let i = 0; i < V.length; i += 2 * k) o.push(V[i], V[i + 1]); return o; }
/* The shift that puts floor A's walls over floor B's (both in metres, y down): exterior walls, columns, shafts and stairs stand
   over each other. Every shift over the two boxes is tried in 50 cm steps, the best ones refined to 2 cm. Returns {dx, dy, f}
   (f: share of A's wall points lying within 25 cm of B's walls) or null when nothing lines up well enough. */
function floorShift(A, B){
  if (!A.length || !B.length) return null; const bA = bbox(A.flatMap(q => q)), bB = bbox(B.flatMap(q => q)), near = nearOf(B), V = sampleOf(A), n = V.length / 2;
  const score = (dx, dy) => { let on = 0; for (let i = 0; i < V.length; i += 2) if (near(V[i] + dx, V[i + 1] + dy) < .25) on++; return on / n; };
  const cost = (dx, dy) => { let c = 0; for (let i = 0; i < V.length; i += 2) c += Math.min(near(V[i] + dx, V[i + 1] + dy), .8); return c / n; };
  const xs = [bB[0] - bA[0], bB[2] - bA[2]], ys = [bB[1] - bA[1], bB[3] - bA[3]], x0 = Math.min(...xs) - 2, x1 = Math.max(...xs) + 2, y0 = Math.min(...ys) - 2, y1 = Math.max(...ys) + 2;
  const step = Math.max(.5, Math.sqrt((x1 - x0) * (y1 - y0) / 900)), G = [];
  for (let dx = x0; dx <= x1; dx += step) for (let dy = y0; dy <= y1; dy += step) G.push([score(dx, dy), dx, dy]);
  let best = null; G.sort((a, b) => b[0] - a[0]).slice(0, 6).forEach(([, dx, dy]) => { let bc = cost(dx, dy);
    for (let r = step / 2; r >= .02; r /= 2) for (let again = true; again;){ again = false; for (const [ex, ey] of [[r, 0], [-r, 0], [0, r], [0, -r]]){ const c = cost(dx + ex, dy + ey); if (c < bc - 1e-9){ bc = c; dx += ex; dy += ey; again = true; } } }
    const f = score(dx, dy); if (!best || f > best.f) best = {dx:Math.round(dx * 100) / 100, dy:Math.round(dy * 100) / 100, f}; });
  return best && best.f >= .4 ? best : null; }
// preview of the whole file: plain lines by role, plan groups outlined
function preview(flat, roles, groups, maxW = 900){
  const segs = flat.segs.filter(s => roles[s.L] && roles[s.L] !== "ignore" && roles[s.L] !== "other"), bb = bbox(segs.flatMap(s => s.p.length > 40 ? [s.p[0], s.p[1], s.p[s.p.length - 2], s.p[s.p.length - 1]] : s.p));
  if (!bb) return "";
  const w = bb[2] - bb[0], h = bb[3] - bb[1], s = maxW / Math.max(w, h * 1.4), C = {wall:"#2b3240", wallExt:"#111722", door:"#a8641f", window:"#2b7bd0", site:"#2e9d57", stair:"#59607a", column:"#59607a", furn:"#c2c7d0", area:"#e0a400"};
  const P = {}; segs.forEach(g => { let d = ""; for (let k = 0; k < g.p.length; k += 2) d += (k ? "L" : "M") + ((g.p[k] - bb[0]) * s).toFixed(1) + " " + ((bb[3] - g.p[k + 1]) * s).toFixed(1); (P[roles[g.L]] = P[roles[g.L]] || []).push(d); });
  const body = Object.entries(P).map(([r, d]) => `<path d="${d.join("")}" stroke="${C[r] || "#888"}" stroke-width="${r === "wallExt" ? 1.3 : r === "furn" ? .5 : .8}" fill="none"/>`).join("");
  const G = groups.map((g, i) => `<rect x="${((g.bb[0] - bb[0]) * s - 4).toFixed(1)}" y="${((bb[3] - g.bb[3]) * s - 4).toFixed(1)}" width="${((g.bb[2] - g.bb[0]) * s + 8).toFixed(1)}" height="${((g.bb[3] - g.bb[1]) * s + 8).toFixed(1)}" fill="none" stroke="#ff7a00" stroke-width="2" stroke-dasharray="8 4"/><text x="${((g.bb[0] - bb[0]) * s).toFixed(1)}" y="${((bb[3] - g.bb[3]) * s - 8).toFixed(1)}" font-size="14" font-weight="700" fill="#ff7a00">${i + 1}${g.title ? " · " + esc(g.title) : ""}</text>`).join("");
  return `<svg viewBox="-10 -24 ${(w * s + 20).toFixed(0)} ${(h * s + 34).toFixed(0)}" width="100%" style="background:#fff;border-radius:8px">${body}${G}</svg>`;
}
const esc = s => String(s).replace(/[&<>"]/g, c => ({"&":"&amp;", "<":"&lt;", ">":"&gt;", '"':"&quot;"}[c]));
return {lroleOf, siteFit, landscape, wallOutlines, nearOf, floorShift, decode, parse, flatten, analyze, floors, build, preview, roleOf, kindOf, bbox, centerLines, mtext, UNITS};
})();
if (typeof module !== "undefined") module.exports = DXF;
