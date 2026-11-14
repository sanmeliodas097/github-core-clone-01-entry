// A standalone GitHub-compatible git forge: git smart HTTP (upload-pack v2/v0,
// receive-pack v0), REST v3, GraphQL v4 and MCP from one process over its own
// in-memory store. Node 22 standard library only; no git binary, no outside
// service, no UI.
//
// The suite's scenario seed is fixed, so the token owner's login is the
// constant below (the scenario's viewer); every other owner reads as 404.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const VIEWER_LOGIN = 'adaiversen';
const VIEWER_ID = 1000;
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const ZERO_OID = '0'.repeat(40);
const JSON_TYPE = 'application/json; charset=utf-8';
const FIXED_TS = 1700000000;
const MERGED_AT = '2026-01-01T00:00:00Z';

// ---------------------------------------------------------------------------
// git objects
// ---------------------------------------------------------------------------

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObj { type: ObjType; data: Buffer }
interface TreeEntry { mode: string; name: string; oid: string }

const TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function sha1(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

function hashObject(type: ObjType, data: Buffer): string {
  const h = createHash('sha1');
  h.update(Buffer.from(`${type} ${data.length}\0`, 'utf8'));
  h.update(data);
  return h.digest('hex');
}

function isOid(s: string): boolean {
  return /^[0-9a-f]{40}$/.test(s);
}

function parseTree(data: Buffer): TreeEntry[] {
  const out: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const nul = data.indexOf(0x00, sp + 1);
    out.push({ mode: data.subarray(off, sp).toString('ascii'), name: data.subarray(sp + 1, nul).toString('utf8'), oid: data.subarray(nul + 1, nul + 21).toString('hex') });
    off = nul + 21;
  }
  return out;
}

function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const x = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
    const y = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
    return Buffer.compare(x, y);
  });
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

interface CommitView { tree: string; parents: string[]; author: string; committer: string; message: string }

function parseCommit(data: Buffer): CommitView {
  const blank = data.indexOf('\n\n');
  const head = blank < 0 ? data.toString('utf8') : data.subarray(0, blank).toString('utf8');
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    const sp = line.indexOf(' ');
    const k = sp < 0 ? line : line.slice(0, sp);
    const v = sp < 0 ? '' : line.slice(sp + 1);
    if (k === 'tree') tree = v;
    else if (k === 'parent') parents.push(v);
    else if (k === 'author') author = v;
    else if (k === 'committer') committer = v;
  }
  return { tree, parents, author, committer, message };
}

function parseTag(data: Buffer): { object: string; type: string; tag: string; tagger: string; message: string } {
  const blank = data.indexOf('\n\n');
  const head = blank < 0 ? data.toString('utf8') : data.subarray(0, blank).toString('utf8');
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  const m = new Map<string, string>();
  for (const line of head.split('\n')) {
    const sp = line.indexOf(' ');
    if (sp > 0) m.set(line.slice(0, sp), line.slice(sp + 1));
  }
  return { object: m.get('object') ?? '', type: m.get('type') ?? '', tag: m.get('tag') ?? '', tagger: m.get('tagger') ?? '', message };
}

// ---------------------------------------------------------------------------
// packfile read / write
// ---------------------------------------------------------------------------

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const readVar = (): number => {
    let v = 0;
    let shift = 0;
    for (;;) {
      const b = delta[off++];
      v += (b & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(b & 0x80)) break;
    }
    return v;
  };
  const srcSize = readVar();
  const tgtSize = readVar();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.allocUnsafe(tgtSize);
  let written = 0;
  while (off < delta.length) {
    const op = delta[off++];
    if (op & 0x80) {
      let cpOff = 0;
      let cpSize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit++) {
        if (op & (1 << bit)) cpOff += delta[off++] * 2 ** shift;
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit++) {
        if (op & (1 << bit)) cpSize += delta[off++] * 2 ** shift;
        shift += 8;
      }
      if (cpSize === 0) cpSize = 0x10000;
      base.copy(out, written, cpOff, cpOff + cpSize);
      written += cpSize;
    } else if (op !== 0) {
      const n = op & 0x7f;
      delta.copy(out, written, off, off + n);
      off += n;
      written += n;
    } else throw new Error('delta opcode 0');
  }
  if (written !== tgtSize) throw new Error('delta size mismatch');
  return out;
}

interface PackObj { type: ObjType; data: Buffer; oid: string }

function readPack(pack: Buffer): Map<string, GitObj> {
  if (pack.length < 32 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack header');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error('bad pack version');
  const count = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  if (sha1(pack.subarray(0, trailerStart)) !== pack.subarray(trailerStart).toString('hex')) throw new Error('pack checksum mismatch');
  interface Raw { offset: number; code: number; size: number; data: Buffer; baseOff?: number; baseOid?: string }
  const raw: Raw[] = [];
  const byOff = new Map<number, Raw>();
  let off = 12;
  for (let i = 0; i < count; i++) {
    const start = off;
    let b = pack[off];
    const first = b;
    let size = b & 0x0f;
    let shift = 4;
    off++;
    while (b & 0x80) {
      b = pack[off++];
      size += (b & 0x7f) * 2 ** shift;
      shift += 7;
    }
    const code = (first >> 4) & 0x07;
    const e: Raw = { offset: start, code, size, data: Buffer.alloc(0) };
    if (code === 6) {
      let byte = pack[off];
      off++;
      let v = byte & 0x7f;
      while (byte & 0x80) {
        byte = pack[off++];
        v = ((v + 1) * 128) + (byte & 0x7f);
      }
      e.baseOff = start - v;
    } else if (code === 7) {
      e.baseOid = pack.subarray(off, off + 20).toString('hex');
      off += 20;
    } else if (!CODE_TYPE[code]) throw new Error('bad pack type');
    const inf = inflateSync(pack.subarray(off, trailerStart), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    if (inf.buffer.length !== size) throw new Error('pack entry size mismatch');
    e.data = inf.buffer;
    off += inf.engine.bytesWritten;
    raw.push(e);
    byOff.set(start, e);
  }
  const out = new Map<string, GitObj>();
  const resolved = new Map<number, PackObj>();
  const byOid = new Map<string, PackObj>();
  const resolve = (e: Raw): PackObj => {
    const cached = resolved.get(e.offset);
    if (cached) return cached;
    let type: ObjType;
    let data: Buffer;
    if (e.code === 6) {
      const base = resolve(byOff.get(e.baseOff!)!);
      type = base.type;
      data = applyDelta(base.data, e.data);
    } else if (e.code === 7) {
      const base = byOid.get(e.baseOid!);
      if (!base) throw new Error('ref-delta base missing');
      type = base.type;
      data = applyDelta(base.data, e.data);
    } else {
      type = CODE_TYPE[e.code]!;
      data = e.data;
    }
    const oid = hashObject(type, data);
    const r: PackObj = { type, data, oid };
    resolved.set(e.offset, r);
    byOid.set(oid, r);
    return r;
  };
  for (const e of raw) {
    const r = resolve(e);
    if (!out.has(r.oid)) out.set(r.oid, { type: r.type, data: r.data });
  }
  return out;
}

function writePackObjectHeader(type: ObjType, size: number): Buffer {
  const code = TYPE_CODE[type];
  const bytes: number[] = [];
  let rem = size;
  let first = (code << 4) | (rem & 0x0f);
  rem = Math.floor(rem / 16);
  while (rem > 0) {
    bytes.push(first | 0x80);
    first = rem & 0x7f;
    rem = Math.floor(rem / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

function writePack(objects: GitObj[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.allocUnsafe(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const o of objects) {
    parts.push(writePackObjectHeader(o.type, o.data.length));
    parts.push(deflateSync(o.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

// ---------------------------------------------------------------------------
// pkt-line
// ---------------------------------------------------------------------------

function pkt(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const h = Buffer.allocUnsafe(4);
  h.write((data.length + 4).toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([h, data]);
}

const FLUSH = Buffer.from('0000', 'ascii');
const DELIM = Buffer.from('0001', 'ascii');

function pktLines(items: Array<string | Buffer | 'flush' | 'delim'>): Buffer {
  const parts: Buffer[] = [];
  for (const it of items) {
    if (it === 'flush') parts.push(FLUSH);
    else if (it === 'delim') parts.push(DELIM);
    else parts.push(pkt(it));
  }
  return Buffer.concat(parts);
}

/** Decode pkt-lines from the front of buf; returns lines and the byte offset where raw data starts. */
function decodePktStream(buf: Buffer): { lines: string[]; offset: number; sawFlush: boolean } {
  const lines: string[] = [];
  let off = 0;
  let sawFlush = false;
  while (off + 4 <= buf.length) {
    const head = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) break;
    const len = parseInt(head, 16);
    if (len === 0) { off += 4; sawFlush = true; break; }
    if (len === 1) { off += 4; continue; }
    if (len === 2) { off += 4; continue; }
    if (len < 4 || off + len > buf.length) break;
    lines.push(buf.subarray(off + 4, off + len).toString('utf8'));
    off += len;
  }
  return { lines, offset: off, sawFlush };
}

// ---------------------------------------------------------------------------
// store
// ---------------------------------------------------------------------------

interface Comment { id: number; gid: string; body: string }
interface Issue { number: number; restId: number; gid: string; title: string; body: string; state: 'open' | 'closed'; labels: string[]; seq: number; comments: Comment[] }
interface Pull { number: number; restId: number; gid: string; title: string; body: string; state: 'open' | 'closed'; merged: boolean; mergedAt: string | null; mergeSha: string | null; head: string; base: string; headSha: string; baseSha: string; mergeBase: string; seq: number }
interface Label { name: string; color: string }
interface Repo {
  name: string; owner: string; description: string; priv: boolean; dbId: number; seq: number;
  refs: Map<string, string>;
  issues: Map<number, Issue>; pulls: Map<number, Pull>; labels: Map<string, Label>;
  nextNum: number; nextComment: number;
}

const objects = new Map<string, GitObj>();
const repos = new Map<string, Repo>();
let nextDbId = 5000;
let nextRestId = 10000;
let seqCounter = 1;
let reqCounter = 1;

function gid(kind: string, ...parts: Array<string | number>): string {
  return Buffer.from(`${kind}:${parts.join(':')}`, 'utf8').toString('base64');
}

function getObject(oid: string): GitObj | undefined {
  return objects.get(oid);
}

function putObject(type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!objects.has(oid)) objects.set(oid, { type, data });
  return oid;
}

/** Flatten a tree to path -> {oid, mode}; follows nested trees. */
function treeToMap(rootOid: string, out = new Map<string, { oid: string; mode: string }>(), prefix = ''): Map<string, { oid: string; mode: string }> {
  const obj = objects.get(rootOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of parseTree(obj.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') treeToMap(e.oid, out, path);
    else out.set(path, { oid: e.oid, mode: e.mode });
  }
  return out;
}

function mapToTree(files: Map<string, { oid: string; mode: string }>): string {
  interface Node { files: Map<string, { oid: string; mode: string }>; dirs: Map<string, Node> }
  const make = (): Node => ({ files: new Map(), dirs: new Map() });
  const root = make();
  for (const [path, v] of files) {
    const segs = path.split('/');
    let node = root;
    for (let i = 0; i < segs.length - 1; i++) {
      const s = segs[i]!;
      if (!node.dirs.has(s)) node.dirs.set(s, make());
      node = node.dirs.get(s)!;
    }
    node.files.set(segs[segs.length - 1]!, v);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, v] of node.files) entries.push({ mode: v.mode, name, oid: v.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return putObject('tree', buildTree(entries));
  };
  return build(root);
}

/** Create a commit on branch (creating the branch if needed); changes map path -> blob bytes or null to delete. */
function makeCommit(repo: Repo, branch: string, changes: Map<string, Buffer | null>, message: string): string {
  const ref = `refs/heads/${branch}`;
  const parent = repo.refs.get(ref);
  const files = new Map<string, { oid: string; mode: string }>();
  if (parent) {
    const c = parseCommit(objects.get(parent)!.data);
    treeToMap(c.tree, files);
  }
  for (const [path, data] of changes) {
    if (data === null) files.delete(path);
    else files.set(path, { oid: putObject('blob', data), mode: '100644' });
  }
  const treeOid = mapToTree(files);
  const ts = FIXED_TS + (seqCounter++);
  const who = `${VIEWER_LOGIN} <${VIEWER_EMAIL}> ${ts} +0000`;
  const lines = [`tree ${treeOid}`];
  if (parent) lines.push(`parent ${parent}`);
  lines.push(`author ${who}`, `committer ${who}`, '');
  const data = Buffer.from(`${lines.join('\n')}\n${message}`, 'utf8');
  const oid = putObject('commit', data);
  repo.refs.set(ref, oid);
  return oid;
}

function isAncestor(ancestor: string, tip: string): boolean {
  if (ancestor === tip) return true;
  const seen = new Set<string>();
  const queue = [tip];
  while (queue.length) {
    const cur = queue.pop()!;
    if (cur === ancestor) return true;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = objects.get(cur);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return false;
}

function mergeBase(a: string, b: string): string {
  const ancA = new Set<string>();
  const queue = [a];
  while (queue.length) {
    const cur = queue.pop()!;
    if (ancA.has(cur)) continue;
    ancA.add(cur);
    const obj = objects.get(cur);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  const queue2 = [b];
  const seen = new Set<string>();
  while (queue2.length) {
    const cur = queue2.pop()!;
    if (ancA.has(cur)) return cur;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = objects.get(cur);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) queue2.push(p);
  }
  return ZERO_OID;
}

/** path -> {old, new} blob oids between two trees (null = absent). */
function treeDiff(baseOid: string, tipOid: string): Map<string, { old: string | null; new: string | null }> {
  const base = baseOid === ZERO_OID ? new Map() : treeToMap(baseOid);
  const tip = tipOid === ZERO_OID ? new Map() : treeToMap(tipOid);
  const out = new Map<string, { old: string | null; new: string | null }>();
  const keys = new Set([...base.keys(), ...tip.keys()]);
  for (const k of keys) {
    const o = base.get(k)?.oid ?? null;
    const n = tip.get(k)?.oid ?? null;
    if (o !== n) out.set(k, { old: o, new: n });
  }
  return out;
}

function resolveTagToCommit(oid: string): string {
  let cur = oid;
  const seen = new Set<string>();
  while (!seen.has(cur)) {
    seen.add(cur);
    const obj = objects.get(cur);
    if (!obj) return cur;
    if (obj.type === 'commit') return cur;
    if (obj.type === 'tag') cur = parseTag(obj.data).object;
    else return cur;
  }
  return cur;
}

// ---------------------------------------------------------------------------
// HTTP plumbing
// ---------------------------------------------------------------------------

function reqId(): string {
  return `req-${reqCounter++}`;
}

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Record<string, string> = {}): void {
  const text = `${JSON.stringify(body)}\n`;
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': Buffer.byteLength(text), 'x-github-request-id': reqId(), ...headers });
  res.end(text);
}

function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length });
  res.end(body);
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (c: Buffer) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function expectedToken(): string {
  return process.env.MAKEFUN_SHOP_TOKEN ?? '';
}

function authOk(req: IncomingMessage): boolean {
  const h = req.headers.authorization ?? '';
  if (!h.startsWith('Bearer ')) return false;
  const tok = h.slice(7);
  if (tok === '') return false;
  const exp = expectedToken();
  if (exp === '') return true;
  return tok === exp;
}

function parseQuery(req: IncomingMessage): { path: string; query: URLSearchParams } {
  try {
    const u = new URL(req.url ?? '/', 'http://entry');
    return { path: u.pathname, query: u.searchParams };
  } catch {
    return { path: '/', query: new URLSearchParams() };
  }
}

function baseOrigin(req: IncomingMessage): string {
  const host = req.headers.host ?? '127.0.0.1';
  return `http://${host}`;
}

// ---------------------------------------------------------------------------
// git smart HTTP
// ---------------------------------------------------------------------------

function sortedRefs(repo: Repo): Array<{ name: string; oid: string }> {
  return [...repo.refs.entries()].map(([name, oid]) => ({ name, oid })).sort((a, b) => (a.name < b.name ? -1 : 1));
}

function gitCapsUpload(): string {
  return 'symref=HEAD:refs/heads/main side-band-64k thin-pack ofs-delta shallow multi_ack_detailed agent=forge/1.0';
}

function gitCapsReceive(): string {
  return 'report-status side-band-64k delete-refs ofs-delta agent=forge/1.0';
}

function v0Advertisement(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps = service === 'git-upload-pack' ? gitCapsUpload() : gitCapsReceive();
  const refs = sortedRefs(repo);
  const lines: Array<string | 'flush'> = [`# service=${service}\n`, 'flush'];
  const refLines: string[] = [];
  if (refs.length === 0) {
    refLines.push(`${ZERO_OID} capabilities^{}\0${caps}\n`);
  } else {
    const mainOid = repo.refs.get('refs/heads/main') ?? refs[0]!.oid;
    refLines.push(`${mainOid} HEAD\0${caps}\n`);
    for (const r of refs) {
      refLines.push(`${r.oid} ${r.name}\n`);
      const obj = objects.get(r.oid);
      if (obj && obj.type === 'tag') {
        const target = resolveTagToCommit(r.oid);
        refLines.push(`${target} ${r.name}^{}\n`);
      }
    }
  }
  for (const l of refLines) lines.push(l);
  lines.push('flush');
  return pktLines(lines);
}

function v2Advertisement(): Buffer {
  return pktLines([
    'version 2\n',
    'agent=forge/1.0\n',
    'ls-refs=unborn\n',
    'fetch=shallow wait-for-done filter\n',
    'server-option\n',
    'object-format=sha1\n',
    'flush',
  ]);
}

function handleInfoRefs(repo: Repo | undefined, service: 'git-upload-pack' | 'git-receive-pack', req: IncomingMessage, res: ServerResponse): void {
  if (!repo) {
    sendJson(res, 404, { message: 'Not Found' });
    return;
  }
  const v2 = service === 'git-upload-pack' && (req.headers['git-protocol'] ?? '') === 'version=2';
  const body = v2 ? v2Advertisement() : v0Advertisement(repo, service);
  sendRaw(res, 200, body, `application/x-${service}-advertisement`);
}

/** Objects reachable from roots; parents of commits in stopAt are not traversed. */
function reachableObjects(roots: string[], stopAt: Set<string>): Set<string> {
  const seen = new Set<string>();
  const queue = [...roots];
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    const obj = objects.get(oid);
    if (!obj) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      queue.push(c.tree);
      if (!stopAt.has(oid)) for (const p of c.parents) queue.push(p);
    } else if (obj.type === 'tag') {
      queue.push(parseTag(obj.data).object);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) queue.push(e.oid);
    }
  }
  return seen;
}

function sidebandPack(pack: Buffer): Buffer {
  const parts: Buffer[] = [];
  for (let off = 0; off < pack.length; off += 32768) {
    const chunk = pack.subarray(off, Math.min(pack.length, off + 32768));
    parts.push(pkt(Buffer.concat([Buffer.from([1]), chunk])));
  }
  return Buffer.concat(parts);
}

interface FetchPlan {
  send: Set<string>;
  shallow: string[];
  unshallow: string[];
}

function planFetch(wants: string[], haves: string[], shallowIn: string[], depth: number | null): FetchPlan {
  const stopAt = new Set(shallowIn);
  const held = reachableObjects(haves, stopAt);
  const shallow: string[] = [];
  const unshallow: string[] = [];
  let send: Set<string>;
  if (depth !== null) {
    // Commits within `depth` generations of a want (want itself is depth 0).
    const included = new Set<string>();
    const dist = new Map<string, number>();
    const queue: string[] = [];
    for (const w of wants) {
      const c = resolveTagToCommit(w);
      if (objects.get(c)?.type === 'commit') { queue.push(c); dist.set(c, 0); }
    }
    while (queue.length) {
      const cur = queue.shift()!;
      const d = dist.get(cur)!;
      if (d >= depth) continue;
      const obj = objects.get(cur);
      if (!obj || obj.type !== 'commit') continue;
      for (const p of parseCommit(obj.data).parents) {
        if (!dist.has(p)) { dist.set(p, d + 1); queue.push(p); }
      }
    }
    for (const [oid, d] of dist) if (d < depth) included.add(oid);
    // Objects: included commits + their trees/blobs (no parent traversal beyond included).
    send = new Set<string>();
    for (const oid of included) {
      send.add(oid);
      const obj = objects.get(oid);
      if (obj && obj.type === 'commit') {
        const c = parseCommit(obj.data);
        for (const x of reachableObjects([c.tree], new Set())) send.add(x);
      }
    }
    for (const oid of included) {
      const obj = objects.get(oid);
      if (!obj || obj.type !== 'commit') continue;
      const parents = parseCommit(obj.data).parents;
      if (parents.some((p) => !included.has(p))) shallow.push(oid);
    }
    for (const b of shallowIn) {
      if (included.has(b)) {
        const obj = objects.get(b);
        const parents = obj && obj.type === 'commit' ? parseCommit(obj.data).parents : [];
        if (parents.every((p) => included.has(p))) unshallow.push(b);
      }
    }
    // Include the tag objects themselves when a want is a tag.
    for (const w of wants) {
      const obj = objects.get(w);
      if (obj && obj.type === 'tag') send.add(w);
    }
  } else {
    const wanted = reachableObjects(wants, new Set());
    send = new Set([...wanted].filter((o) => !held.has(o)));
  }
  for (const h of held) send.delete(h);
  return { send, shallow, unshallow };
}

function handleUploadPack(repo: Repo, req: IncomingMessage, res: ServerResponse, body: Buffer): void {
  const v2 = (req.headers['git-protocol'] ?? '') === 'version=2';
  try {
    const { lines } = decodePktStream(body);
    if (v2) {
      const command = lines.find((l) => l.startsWith('command='))?.slice(8).trim() ?? '';
      if (command === 'ls-refs') {
        const peel = lines.some((l) => l.trim() === 'peel');
        const symrefs = lines.some((l) => l.trim() === 'symrefs');
        const prefixes = lines.filter((l) => l.startsWith('ref-prefix ')).map((l) => l.slice(11).trim());
        const out: string[] = [];
        const mainOid = repo.refs.get('refs/heads/main');
        const headLine = mainOid
          ? `${mainOid} HEAD${symrefs ? ' symref-target:refs/heads/main' : ''}\n`
          : `unborn HEAD${symrefs ? ' symref-target:refs/heads/main' : ''}\n`;
        const anyMatch = prefixes.length === 0;
        if (anyMatch) out.push(headLine);
        for (const r of sortedRefs(repo)) {
          if (prefixes.length && !prefixes.some((p) => r.name.startsWith(p))) continue;
          let line = `${r.oid} ${r.name}`;
          const obj = objects.get(r.oid);
          if (peel && obj && obj.type === 'tag') line += ` peeled:${resolveTagToCommit(r.oid)}`;
          out.push(`${line}\n`);
        }
        sendRaw(res, 200, Buffer.concat([pktLines(out), FLUSH]), 'application/x-git-upload-pack-result');
        return;
      }
      if (command === 'fetch') {
        const wants = lines.filter((l) => l.startsWith('want ')).map((l) => l.slice(5).trim().split(' ')[0]!);
        const haves = lines.filter((l) => l.startsWith('have ')).map((l) => l.slice(5).trim());
        const shallowIn = lines.filter((l) => l.startsWith('shallow ')).map((l) => l.slice(8).trim());
        const deepenLine = lines.find((l) => l.startsWith('deepen '));
        const depth = deepenLine ? Number(deepenLine.slice(7).trim()) : null;
        const plan = planFetch(wants, haves, shallowIn, depth);
        const packObjs: GitObj[] = [];
        for (const oid of plan.send) {
          const o = objects.get(oid);
          if (o) packObjs.push(o);
        }
        packObjs.sort((a, b) => (a.type < b.type ? -1 : 1));
        const pack = writePack(packObjs);
        const parts: Buffer[] = [];
        parts.push(pkt('acknowledgments\n'), pkt('NAK\n'), DELIM);
        if (plan.shallow.length || plan.unshallow.length) {
          parts.push(pkt('shallow-info\n'));
          for (const s of plan.shallow) parts.push(pkt(`shallow ${s}\n`));
          for (const s of plan.unshallow) parts.push(pkt(`unshallow ${s}\n`));
          parts.push(DELIM);
        }
        parts.push(pkt('packfile\n'));
        parts.push(sidebandPack(pack));
        parts.push(FLUSH);
        sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
        return;
      }
      sendRaw(res, 400, Buffer.from('unknown v2 command', 'utf8'), 'text/plain');
      return;
    }
    // v0 fetch: want lines, shallow/deepen, flush, have lines, done, flush.
    const wants = lines.filter((l) => l.startsWith('want ')).map((l) => l.slice(5).trim().split(' ')[0]!);
    const haves = lines.filter((l) => l.startsWith('have ')).map((l) => l.slice(5).trim());
    const shallowIn = lines.filter((l) => l.startsWith('shallow ')).map((l) => l.slice(8).trim());
    const deepenLine = lines.find((l) => l.startsWith('deepen '));
    const depth = deepenLine ? Number(deepenLine.slice(7).trim()) : null;
    if (wants.length === 0 || wants.some((w) => !isOid(w))) {
      sendRaw(res, 400, Buffer.from('bad fetch request', 'utf8'), 'text/plain');
      return;
    }
    const plan = planFetch(wants, haves, shallowIn, depth);
    const packObjs: GitObj[] = [];
    for (const oid of plan.send) {
      const o = objects.get(oid);
      if (o) packObjs.push(o);
    }
    const pack = writePack(packObjs);
    const parts: Buffer[] = [pkt('NAK\n')];
    for (const s of plan.shallow) parts.push(pkt(`shallow ${s}\n`));
    for (const s of plan.unshallow) parts.push(pkt(`unshallow ${s}\n`));
    parts.push(sidebandPack(pack));
    parts.push(FLUSH);
    sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
  } catch (err) {
    sendRaw(res, 400, Buffer.from(`fetch failed: ${err instanceof Error ? err.message : String(err)}`, 'utf8'), 'text/plain');
  }
}

function handleReceivePack(repo: Repo, req: IncomingMessage, res: ServerResponse, body: Buffer): void {
  const report = (unpackOk: boolean, unpackDetail: string, refs: Array<{ ref: string; ok: boolean; reason: string }>): void => {
    const inner: Array<string | 'flush'> = [`unpack ${unpackOk ? 'ok' : unpackDetail}\n`];
    for (const r of refs) inner.push(r.ok ? `ok ${r.ref}\n` : `ng ${r.ref} ${r.reason}\n`);
    inner.push('flush');
    const band1 = pktLines(inner);
    const outer = pkt(Buffer.concat([Buffer.from([1]), band1]));
    sendRaw(res, 200, Buffer.concat([outer, FLUSH]), 'application/x-git-receive-pack-result');
  };
  try {
    const { lines, offset } = decodePktStream(body);
    if (lines.length === 0) {
      report(false, 'no commands', []);
      return;
    }
    const commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
    for (const line of lines) {
      const nul = line.indexOf('\0');
      const clean = nul >= 0 ? line.slice(0, nul) : line;
      const parts = clean.trim().split(' ');
      if (parts.length < 3 || !isOid(parts[0]!) || !isOid(parts[1]!)) continue;
      commands.push({ oldOid: parts[0]!, newOid: parts[1]!, ref: parts[2]! });
    }
    if (commands.length === 0) {
      report(false, 'no commands', []);
      return;
    }
    const hasUpdates = commands.some((c) => c.newOid !== ZERO_OID);
    let unpacked = new Map<string, GitObj>();
    if (hasUpdates) {
      const packBytes = body.subarray(offset);
      if (packBytes.length > 0) {
        try {
          unpacked = readPack(packBytes);
        } catch (err) {
          report(false, `unpacker error: ${err instanceof Error ? err.message : String(err)}`, commands.map((c) => ({ ref: c.ref, ok: false, reason: 'unpack failed' })));
          return;
        }
        for (const [oid, obj] of unpacked) {
          if (hashObject(obj.type, obj.data) !== oid) {
            report(false, 'unpacker error: object hash mismatch', commands.map((c) => ({ ref: c.ref, ok: false, reason: 'unpack failed' })));
            return;
          }
          if (!objects.has(oid)) objects.set(oid, obj);
        }
      }
    }
    const results: Array<{ ref: string; ok: boolean; reason: string }> = [];
    for (const cmd of commands) {
      const current = repo.refs.get(cmd.ref);
      if (cmd.newOid === ZERO_OID) {
        // delete
        if (!current) { results.push({ ref: cmd.ref, ok: false, reason: 'remote ref does not exist' }); continue; }
        if (cmd.oldOid !== ZERO_OID && cmd.oldOid !== current) { results.push({ ref: cmd.ref, ok: false, reason: 'non-fast-forward' }); continue; }
        repo.refs.delete(cmd.ref);
        results.push({ ref: cmd.ref, ok: true, reason: '' });
        continue;
      }
      const newObj = objects.get(cmd.newOid);
      if (!newObj) { results.push({ ref: cmd.ref, ok: false, reason: 'object not found' }); continue; }
      if (!current) {
        if (cmd.oldOid !== ZERO_OID) { results.push({ ref: cmd.ref, ok: false, reason: 'non-fast-forward' }); continue; }
        // create: closure must exist
        let missing = false;
        try { reachableObjects([cmd.newOid], new Set()); } catch { missing = true; }
        if (missing) { results.push({ ref: cmd.ref, ok: false, reason: 'object not found' }); continue; }
        repo.refs.set(cmd.ref, cmd.newOid);
        results.push({ ref: cmd.ref, ok: true, reason: '' });
        continue;
      }
      if (cmd.oldOid !== current) { results.push({ ref: cmd.ref, ok: false, reason: 'non-fast-forward' }); continue; }
      if (newObj.type === 'commit' && !isAncestor(current, cmd.newOid)) {
        results.push({ ref: cmd.ref, ok: false, reason: 'non-fast-forward' });
        continue;
      }
      repo.refs.set(cmd.ref, cmd.newOid);
      results.push({ ref: cmd.ref, ok: true, reason: '' });
    }
    report(true, 'ok', results);
  } catch (err) {
    try {
      report(false, `unpacker error: ${err instanceof Error ? err.message : String(err)}`, []);
    } catch {
      sendRaw(res, 400, Buffer.from('bad receive-pack request', 'utf8'), 'text/plain');
    }
  }
}

// ---------------------------------------------------------------------------
// REST v3
// ---------------------------------------------------------------------------

function repoObject(repo: Repo): Record<string, unknown> {
  return {
    id: repo.dbId,
    node_id: gid('Repository', repo.dbId),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER_ID, type: 'User' },
    private: repo.priv,
    description: repo.description,
    default_branch: 'main',
    html_url: `https://example.invalid/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    created_at: '2025-01-01T00:00:00Z',
    updated_at: '2025-01-01T00:00:00Z',
    pushed_at: '2025-01-01T00:00:00Z',
    git_url: `git://example.invalid/${repo.owner}/${repo.name}.git`,
    ssh_url: `git@example.invalid:${repo.owner}/${repo.name}.git`,
    clone_url: `https://example.invalid/${repo.owner}/${repo.name}.git`,
    homepage: null,
    language: null,
    forks_count: 0,
    stargazers_count: 0,
    watchers_count: 0,
    open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
    has_issues: true,
    has_projects: true,
    has_wiki: true,
    has_pages: false,
    archived: false,
    disabled: false,
    visibility: repo.priv ? 'private' : 'public',
    license: null,
    topics: [],
  };
}

function issueObject(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: issue.restId,
    node_id: issue.gid,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((n) => {
      const l = repo.labels.get(n);
      return { name: n, color: l?.color ?? 'ededed', description: '' };
    }),
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    assignees: [],
    locked: false,
    comments: issue.comments.length,
    created_at: '2025-01-01T00:00:00Z',
    updated_at: '2025-01-01T00:00:00Z',
    closed_at: issue.state === 'closed' ? '2025-01-02T00:00:00Z' : null,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
  };
}

function pullObject(repo: Repo, pr: Pull): Record<string, unknown> {
  return {
    id: pr.restId,
    node_id: pr.gid,
    number: pr.number,
    title: pr.title,
    body: pr.body,
    state: pr.state,
    merged: pr.merged,
    mergeable: prMergeable(repo, pr),
    merge_commit_sha: pr.mergeSha,
    merged_at: pr.mergedAt,
    head: { ref: pr.head, sha: pr.headSha, label: `${repo.owner}:${pr.head}`, user: { login: VIEWER_LOGIN, id: VIEWER_ID } },
    base: { ref: pr.base, sha: pr.baseSha, label: `${repo.owner}:${pr.base}`, user: { login: VIEWER_LOGIN, id: VIEWER_ID } },
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    created_at: '2025-01-01T00:00:00Z',
    updated_at: '2025-01-01T00:00:00Z',
    closed_at: pr.state === 'closed' ? '2025-01-02T00:00:00Z' : null,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/pull/${pr.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pr.number}`,
  };
}

function prMergeable(repo: Repo, pr: Pull): string {
  if (pr.state !== 'open') return 'UNKNOWN';
  const baseTip = repo.refs.get(`refs/heads/${pr.base}`);
  if (!baseTip) return 'UNKNOWN';
  if (baseTip === pr.mergeBase || isAncestor(baseTip, pr.headSha)) return 'MERGEABLE';
  const headDiff = treeDiff(pr.mergeBase === ZERO_OID ? ZERO_OID : parseCommit(objects.get(pr.mergeBase)!.data).tree, parseCommit(objects.get(pr.headSha)!.data).tree);
  const baseDiff = treeDiff(pr.mergeBase === ZERO_OID ? ZERO_OID : parseCommit(objects.get(pr.mergeBase)!.data).tree, parseCommit(objects.get(baseTip)!.data).tree);
  for (const [path, h] of headDiff) {
    const b = baseDiff.get(path);
    if (b && b.new !== h.new) return 'CONFLICTING';
  }
  return 'MERGEABLE';
}

function prFiles(repo: Repo, pr: Pull): Array<Record<string, unknown>> {
  const baseTree = pr.mergeBase === ZERO_OID ? ZERO_OID : parseCommit(objects.get(pr.mergeBase)!.data).tree;
  const headTree = parseCommit(objects.get(pr.headSha)!.data).tree;
  const diff = treeDiff(baseTree, headTree);
  const out: Array<Record<string, unknown>> = [];
  for (const [path, d] of [...diff.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1))) {
    const oldText = d.old ? objects.get(d.old)?.data.toString('utf8') ?? '' : '';
    const newText = d.new ? objects.get(d.new)?.data.toString('utf8') ?? '' : '';
    const oldLines = oldText === '' ? [] : oldText.split('\n');
    const newLines = newText === '' ? [] : newText.split('\n');
    const oldSet = new Map<string, number>();
    for (const l of oldLines) oldSet.set(l, (oldSet.get(l) ?? 0) + 1);
    const newSet = new Map<string, number>();
    for (const l of newLines) newSet.set(l, (newSet.get(l) ?? 0) + 1);
    let additions = 0;
    let deletions = 0;
    for (const [l, n] of newSet) additions += Math.max(0, n - (oldSet.get(l) ?? 0));
    for (const [l, n] of oldSet) deletions += Math.max(0, n - (newSet.get(l) ?? 0));
    const status = d.old === null ? 'added' : d.new === null ? 'removed' : 'modified';
    out.push({ filename: path, status, additions, deletions, changes: additions + deletions, blob_url: '', raw_url: '', contents_url: '' });
  }
  return out;
}

function createIssueIn(repo: Repo, title: string, body: string, labels: string[]): Issue | { error: string } {
  for (const l of labels) if (!repo.labels.has(l)) return { error: `Label '${l}' does not exist` };
  const number = repo.nextNum++;
  const issue: Issue = {
    number,
    restId: nextRestId++,
    gid: gid('Issue', repo.dbId, number),
    title,
    body: body ?? '',
    state: 'open',
    labels: [...labels],
    seq: seqCounter++,
    comments: [],
  };
  repo.issues.set(number, issue);
  return issue;
}

function createPullIn(repo: Repo, title: string, body: string, head: string, base: string): Pull | { error: string } {
  const headSha = repo.refs.get(`refs/heads/${head}`);
  const baseSha = repo.refs.get(`refs/heads/${base}`);
  if (!headSha || !baseSha) return { error: 'head or base branch does not exist' };
  for (const p of repo.pulls.values()) {
    if (p.state === 'open' && p.head === head && p.base === base) return { error: 'A pull request already exists for this head and base' };
  }
  const number = repo.nextNum++;
  const mb = mergeBase(headSha, baseSha);
  const pr: Pull = {
    number,
    restId: nextRestId++,
    gid: gid('PullRequest', repo.dbId, number),
    title,
    body: body ?? '',
    state: 'open',
    merged: false,
    mergedAt: null,
    mergeSha: null,
    head,
    base,
    headSha,
    baseSha,
    mergeBase: mb,
    seq: seqCounter++,
  };
  repo.pulls.set(number, pr);
  return pr;
}

function doMerge(repo: Repo, pr: Pull): { sha: string } | { error: string; status: number } {
  if (pr.state !== 'open') return { error: 'Pull request is already closed', status: 405 };
  if (prMergeable(repo, pr) === 'CONFLICTING') return { error: 'Merge conflict', status: 405 };
  const baseTip = repo.refs.get(`refs/heads/${pr.base}`)!;
  const baseTree = parseCommit(objects.get(baseTip)!.data).tree;
  const headTree = parseCommit(objects.get(pr.headSha)!.data).tree;
  const mbTree = pr.mergeBase === ZERO_OID ? ZERO_OID : parseCommit(objects.get(pr.mergeBase)!.data).tree;
  const files = treeToMap(baseTree);
  const diff = treeDiff(mbTree, headTree);
  for (const [path, d] of diff) {
    if (d.new === null) files.delete(path);
    else files.set(path, { oid: d.new, mode: '100644' });
  }
  const treeOid = mapToTree(files);
  const ts = FIXED_TS + (seqCounter++);
  const who = `${VIEWER_LOGIN} <${VIEWER_EMAIL}> ${ts} +0000`;
  const msg = `Merge pull request #${pr.number} from ${pr.head}\n\n${pr.title}`;
  const data = Buffer.from(`tree ${treeOid}\nparent ${baseTip}\nauthor ${who}\ncommitter ${who}\n\n${msg}`, 'utf8');
  const sha = putObject('commit', data);
  repo.refs.set(`refs/heads/${pr.base}`, sha);
  pr.state = 'closed';
  pr.merged = true;
  pr.mergedAt = MERGED_AT;
  pr.mergeSha = sha;
  return { sha };
}

function paginate<T>(items: T[], query: URLSearchParams, req: IncomingMessage, path: string): { page: T[]; link: string | null } {
  const perPage = Math.max(1, Math.min(100, Number(query.get('per_page') ?? '30') || 30));
  const page = Math.max(1, Number(query.get('page') ?? '1') || 1);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  let link: string | null = null;
  if (start + perPage < items.length) {
    const url = new URL(`${baseOrigin(req)}${path}`);
    url.searchParams.set('per_page', String(perPage));
    url.searchParams.set('page', String(page + 1));
    link = `<${url.toString()}>; rel="next"`;
  }
  return { page: slice, link };
}

function parseJsonBody(body: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (body.length === 0) return { ok: true, value: {} };
  try {
    return { ok: true, value: JSON.parse(body.toString('utf8')) as unknown };
  } catch {
    return { ok: false };
  }
}

function asRecord(v: unknown): Record<string, unknown> {
  return v !== null && typeof v === 'object' && !Array.isArray(v) ? (v as Record<string, unknown>) : {};
}

function lookupRepo(owner: string, name: string): Repo | undefined {
  if (owner !== VIEWER_LOGIN) return undefined;
  return repos.get(name);
}

async function handleRest(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const { path, query } = parseQuery(req);
  const method = req.method ?? 'GET';
  const seg = path.split('/').filter((s) => s !== '');
  // seg[0] === 'api', seg[1] === 'v3'
  if (!authOk(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  const bodyBuf = method === 'GET' || method === 'HEAD' ? Buffer.alloc(0) : await readBody(req);
  const parsed = bodyBuf.length ? parseJsonBody(bodyBuf) : { ok: true as const, value: {} as unknown };
  if (!parsed.ok) {
    sendJson(res, 400, { message: 'Problems parsing JSON' });
    return;
  }
  const body = asRecord(parsed.value);

  // GET /api/v3/ and /api/v3
  if (seg.length === 2 && method === 'GET') {
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
    return;
  }
  // GET /api/v3/meta
  if (seg.length === 3 && seg[2] === 'meta' && method === 'GET') {
    sendJson(res, 200, { installed_version: '1.0.0', installed_at: '2025-01-01T00:00:00Z' });
    return;
  }
  // GET /api/v3/user
  if (seg.length === 3 && seg[2] === 'user' && method === 'GET') {
    sendJson(res, 200, { login: VIEWER_LOGIN, id: VIEWER_ID, name: VIEWER_NAME, email: VIEWER_EMAIL, type: 'User' });
    return;
  }
  // GET /api/v3/user/repos ; POST /api/v3/user/repos
  if (seg.length === 4 && seg[2] === 'user' && seg[3] === 'repos') {
    if (method === 'GET') {
      const all = [...repos.values()].sort((a, b) => a.seq - b.seq).map(repoObject);
      const { page, link } = paginate(all, query, req, path);
      sendJson(res, 200, page, link ? { link } : {});
      return;
    }
    if (method === 'POST') {
      const name = typeof body.name === 'string' ? body.name : '';
      if (name === '') { sendJson(res, 422, { message: 'name is required' }); return; }
      if (repos.has(name)) { sendJson(res, 422, { message: 'Repository already exists' }); return; }
      const repo: Repo = {
        name, owner: VIEWER_LOGIN,
        description: typeof body.description === 'string' ? body.description : '',
        priv: body.private === true,
        dbId: nextDbId++, seq: seqCounter++,
        refs: new Map(), issues: new Map(), pulls: new Map(), labels: new Map(),
        nextNum: 1, nextComment: 1,
      };
      repos.set(name, repo);
      sendJson(res, 201, repoObject(repo));
      return;
    }
  }
  // /api/v3/repos/{owner}/{repo}[...]
  if (seg.length >= 5 && seg[2] === 'repos') {
    const owner = decodeURIComponent(seg[3]!);
    const name = decodeURIComponent(seg[4]!);
    const repo = lookupRepo(owner, name);
    if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return; }
    const rest = seg.slice(5);
    // GET/PATCH/DELETE repo itself
    if (rest.length === 0) {
      if (method === 'GET') { sendJson(res, 200, repoObject(repo)); return; }
      if (method === 'PATCH') {
        if (typeof body.description === 'string') repo.description = body.description;
        sendJson(res, 200, repoObject(repo));
        return;
      }
      if (method === 'DELETE') {
        repos.delete(name);
        res.writeHead(204, { 'x-github-request-id': reqId() });
        res.end();
        return;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return;
    }
    // branches
    if (rest[0] === 'branches') {
      if (rest.length === 1 && method === 'GET') {
        const list = [...repo.refs.entries()]
          .filter(([n]) => n.startsWith('refs/heads/'))
          .map(([n, oid]) => ({ name: n.slice(11), commit: { sha: oid }, protected: false }))
          .sort((a, b) => (a.name < b.name ? -1 : 1));
        sendJson(res, 200, list);
        return;
      }
      if (rest.length === 2 && method === 'GET') {
        const oid = repo.refs.get(`refs/heads/${decodeURIComponent(rest[1]!)}`);
        if (!oid) { sendJson(res, 404, { message: 'Not Found' }); return; }
        sendJson(res, 200, { name: decodeURIComponent(rest[1]!), commit: { sha: oid }, protected: false });
        return;
      }
    }
    // git/refs
    if (rest[0] === 'git' && rest[1] === 'refs') {
      if (method === 'POST' && rest.length === 2) {
        const ref = typeof body.ref === 'string' ? body.ref : '';
        const sha = typeof body.sha === 'string' ? body.sha : '';
        if (!ref.startsWith('refs/') || !isOid(sha) || !objects.has(sha)) { sendJson(res, 422, { message: 'Invalid ref or sha' }); return; }
        repo.refs.set(ref, sha);
        sendJson(res, 201, { ref, object: { sha, type: objects.get(sha)?.type ?? 'commit' }, url: '' });
        return;
      }
      if (method === 'GET' && rest.length >= 4 && rest[2] === 'heads') {
        const branch = decodeURIComponent(rest.slice(3).join('/'));
        const oid = repo.refs.get(`refs/heads/${branch}`);
        if (!oid) { sendJson(res, 404, { message: 'Not Found' }); return; }
        sendJson(res, 200, { ref: `refs/heads/${branch}`, object: { sha: oid, type: 'commit' } });
        return;
      }
      if (method === 'GET' && rest.length === 2) {
        const list = [...repo.refs.entries()].map(([n, oid]) => ({ ref: n, object: { sha: oid } }));
        sendJson(res, 200, list);
        return;
      }
    }
    // commits
    if (rest[0] === 'commits' && rest.length === 1 && method === 'GET') {
      const refName = query.get('sha') ?? 'main';
      const tip = repo.refs.get(`refs/heads/${refName}`) ?? (isOid(refName) ? refName : undefined);
      const out: Array<Record<string, unknown>> = [];
      if (tip && objects.get(tip)?.type === 'commit') {
        const seen = new Set<string>();
        let cur: string | undefined = tip;
        while (cur && !seen.has(cur)) {
          seen.add(cur);
          const obj = objects.get(cur);
          if (!obj || obj.type !== 'commit') break;
          const c = parseCommit(obj.data);
          out.push({ sha: cur, commit: { message: c.message, author: { name: VIEWER_LOGIN, email: VIEWER_EMAIL }, committer: { name: VIEWER_LOGIN, email: VIEWER_EMAIL } }, parents: c.parents.map((p) => ({ sha: p })) });
          cur = c.parents[0];
        }
      }
      sendJson(res, 200, out);
      return;
    }
    // contents
    if (rest[0] === 'contents') {
      const filePath = rest.slice(1).map((s) => decodeURIComponent(s)).join('/');
      const refName = query.get('ref') ?? 'main';
      const tip = repo.refs.get(`refs/heads/${refName}`);
      if (method === 'GET') {
        if (!tip) { sendJson(res, 404, { message: 'Not Found' }); return; }
        const treeOid = parseCommit(objects.get(tip)!.data).tree;
        const files = treeToMap(treeOid);
        const hit = files.get(filePath);
        if (hit) {
          const data = objects.get(hit.oid)!.data;
          sendJson(res, 200, { type: 'file', encoding: 'base64', size: data.length, name: filePath.split('/').pop(), path: filePath, content: data.toString('base64'), sha: hit.oid });
          return;
        }
        // directory?
        const prefix = filePath === '' ? '' : `${filePath}/`;
        const entries: Array<Record<string, unknown>> = [];
        const seenDirs = new Set<string>();
        for (const [p, v] of files) {
          if (prefix !== '' && !p.startsWith(prefix)) continue;
          const rel = prefix === '' ? p : p.slice(prefix.length);
          const slash = rel.indexOf('/');
          if (slash >= 0) {
            const dir = rel.slice(0, slash);
            if (!seenDirs.has(dir)) {
              seenDirs.add(dir);
              entries.push({ type: 'dir', name: dir, path: prefix + dir, sha: '' });
            }
          } else {
            entries.push({ type: 'file', name: rel, path: p, sha: v.oid, size: objects.get(v.oid)?.data.length ?? 0 });
          }
        }
        if (entries.length === 0) { sendJson(res, 404, { message: 'Not Found' }); return; }
        entries.sort((a, b) => String(a.name) < String(b.name) ? -1 : 1);
        sendJson(res, 200, entries);
        return;
      }
      if (method === 'PUT') {
        const branch = typeof body.branch === 'string' ? body.branch : 'main';
        const message = typeof body.message === 'string' ? body.message : 'update';
        const contentB64 = typeof body.content === 'string' ? body.content : '';
        const sha = typeof body.sha === 'string' ? body.sha : undefined;
        let content: Buffer;
        try { content = Buffer.from(contentB64, 'base64'); } catch { sendJson(res, 400, { message: 'Invalid base64 content' }); return; }
        const branchRef = `refs/heads/${branch}`;
        let branchTip = repo.refs.get(branchRef);
        if (!branchTip) {
          // New branch: start from the default branch tip (or unborn).
          const baseTip = repo.refs.get('refs/heads/main');
          if (baseTip && branch !== 'main') branchTip = baseTip;
        }
        if (branchTip) {
          const treeOid = parseCommit(objects.get(branchTip)!.data).tree;
          const files = treeToMap(treeOid);
          const existing = files.get(filePath);
          if (existing) {
            if (sha !== undefined && sha.toLowerCase() !== existing.oid.toLowerCase()) { sendJson(res, 409, { message: 'sha does not match' }); return; }
          }
        }
        const blobOid = putObject('blob', content);
        const commitSha = makeCommit(repo, branch, new Map([[filePath, content]]), message);
        const isUpdate = branchTip !== undefined && (() => {
          const treeOid = parseCommit(objects.get(branchTip!)!.data).tree;
          return treeToMap(treeOid).has(filePath);
        })();
        sendJson(res, isUpdate ? 200 : 201, {
          content: { name: filePath.split('/').pop(), path: filePath, sha: blobOid, size: content.length, type: 'file', encoding: 'base64' },
          commit: { sha: commitSha, message },
        });
        return;
      }
      if (method === 'DELETE') {
        const branch = typeof body.branch === 'string' ? body.branch : 'main';
        const sha = typeof body.sha === 'string' ? body.sha : undefined;
        const message = typeof body.message === 'string' ? body.message : 'delete';
        const branchTip = repo.refs.get(`refs/heads/${branch}`);
        if (!branchTip) { sendJson(res, 404, { message: 'Not Found' }); return; }
        const treeOid = parseCommit(objects.get(branchTip)!.data).tree;
        const files = treeToMap(treeOid);
        const existing = files.get(filePath);
        if (!existing) { sendJson(res, 404, { message: 'Not Found' }); return; }
        if (sha !== undefined && sha.toLowerCase() !== existing.oid.toLowerCase()) { sendJson(res, 409, { message: 'sha does not match' }); return; }
        const commitSha = makeCommit(repo, branch, new Map([[filePath, null]]), message);
        sendJson(res, 200, { commit: { sha: commitSha, message } });
        return;
      }
    }
    // labels
    if (rest[0] === 'labels') {
      if (method === 'POST' && rest.length === 1) {
        const name = typeof body.name === 'string' ? body.name : '';
        const color = typeof body.color === 'string' ? body.color : 'ededed';
        if (name === '') { sendJson(res, 422, { message: 'name is required' }); return; }
        repo.labels.set(name, { name, color });
        sendJson(res, 201, { name, color, description: '' });
        return;
      }
      if (method === 'GET' && rest.length === 1) {
        sendJson(res, 200, [...repo.labels.values()].map((l) => ({ name: l.name, color: l.color, description: '' })));
        return;
      }
    }
    // issues
    if (rest[0] === 'issues') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = typeof body.title === 'string' ? body.title : '';
          const b = typeof body.body === 'string' ? body.body : '';
          const labels = Array.isArray(body.labels) ? body.labels.filter((x): x is string => typeof x === 'string') : [];
          if (title === '') { sendJson(res, 422, { message: 'title is required' }); return; }
          const created = createIssueIn(repo, title, b, labels);
          if ('error' in created) { sendJson(res, 422, { message: created.error }); return; }
          sendJson(res, 201, issueObject(repo, created));
          return;
        }
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          const sort = query.get('sort') ?? 'created';
          const dir = query.get('direction') ?? 'desc';
          let list = [...repo.issues.values()];
          if (state !== 'all') list = list.filter((i) => i.state === state);
          if (sort === 'created') list.sort((a, b) => (dir === 'asc' ? a.seq - b.seq : b.seq - a.seq));
          else list.sort((a, b) => b.seq - a.seq);
          const { page, link } = paginate(list.map((i) => issueObject(repo, i)), query, req, path);
          sendJson(res, 200, page, link ? { link } : {});
          return;
        }
      }
      if (rest.length === 2) {
        const num = Number(rest[1]);
        const issue = repo.issues.get(num);
        if (!issue) { sendJson(res, 404, { message: 'Not Found' }); return; }
        if (method === 'GET') { sendJson(res, 200, issueObject(repo, issue)); return; }
        if (method === 'PATCH') {
          if (body.state === 'open' || body.state === 'closed') issue.state = body.state;
          if (typeof body.title === 'string') issue.title = body.title;
          if (typeof body.body === 'string') issue.body = body.body;
          sendJson(res, 200, issueObject(repo, issue));
          return;
        }
      }
      if (rest.length === 3 && rest[2] === 'comments') {
        const num = Number(rest[1]);
        const issue = repo.issues.get(num);
        if (!issue) { sendJson(res, 404, { message: 'Not Found' }); return; }
        if (method === 'POST') {
          const b = typeof body.body === 'string' ? body.body : '';
          const id = repo.nextComment++;
          const c: Comment = { id, gid: gid('IssueComment', repo.dbId, num, id), body: b };
          issue.comments.push(c);
          sendJson(res, 201, { id, node_id: c.gid, body: b, user: { login: VIEWER_LOGIN, id: VIEWER_ID } });
          return;
        }
        if (method === 'GET') {
          sendJson(res, 200, issue.comments.map((c) => ({ id: c.id, node_id: c.gid, body: c.body, user: { login: VIEWER_LOGIN, id: VIEWER_ID } })));
          return;
        }
      }
    }
    // pulls
    if (rest[0] === 'pulls') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = typeof body.title === 'string' ? body.title : '';
          const b = typeof body.body === 'string' ? body.body : '';
          const head = typeof body.head === 'string' ? body.head : '';
          const base = typeof body.base === 'string' ? body.base : 'main';
          if (title === '' || head === '') { sendJson(res, 422, { message: 'title and head are required' }); return; }
          const created = createPullIn(repo, title, b, head, base);
          if ('error' in created) { sendJson(res, 422, { message: created.error }); return; }
          sendJson(res, 201, pullObject(repo, created));
          return;
        }
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          let list = [...repo.pulls.values()];
          if (state !== 'all') list = list.filter((p) => p.state === state);
          list.sort((a, b) => b.seq - a.seq);
          const { page, link } = paginate(list.map((p) => pullObject(repo, p)), query, req, path);
          sendJson(res, 200, page, link ? { link } : {});
          return;
        }
      }
      if (rest.length === 2) {
        const num = Number(rest[1]);
        const pr = repo.pulls.get(num);
        if (!pr) { sendJson(res, 404, { message: 'Not Found' }); return; }
        if (method === 'GET') { sendJson(res, 200, pullObject(repo, pr)); return; }
      }
      if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
        const num = Number(rest[1]);
        const pr = repo.pulls.get(num);
        if (!pr) { sendJson(res, 404, { message: 'Not Found' }); return; }
        sendJson(res, 200, prFiles(repo, pr));
        return;
      }
      if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
        const num = Number(rest[1]);
        const pr = repo.pulls.get(num);
        if (!pr) { sendJson(res, 404, { message: 'Not Found' }); return; }
        const merged = doMerge(repo, pr);
        if ('error' in merged) { sendJson(res, merged.status, { message: merged.error }); return; }
        sendJson(res, 200, { sha: merged.sha, merged: true, message: `Pull Request #${num} merged` });
        return;
      }
    }
  }
  sendJson(res, 404, { message: 'Not Found' });
}

// ---------------------------------------------------------------------------
// GraphQL v4
// ---------------------------------------------------------------------------

type GqlValue =
  | { kind: 'var'; name: string }
  | { kind: 'string'; value: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'bool'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Array<{ name: string; value: GqlValue }> };

interface GqlSel {
  alias: string | null;
  name: string;
  args: Array<{ name: string; value: GqlValue }>;
  children: GqlSel[] | null;
  fragName: string | null;
  fragType: string | null;
}

interface GqlOp {
  type: 'query' | 'mutation';
  name: string | null;
  selections: GqlSel[];
}

class GqlParser {
  private pos = 0;
  private readonly src: string;
  constructor(src: string) { this.src = src; }

  private skipWs(): void {
    for (;;) {
      while (this.pos < this.src.length && /\s/.test(this.src[this.pos]!)) this.pos++;
      if (this.src[this.pos] === '#') {
        while (this.pos < this.src.length && this.src[this.pos] !== '\n') this.pos++;
        continue;
      }
      break;
    }
  }

  private peek(): string {
    this.skipWs();
    return this.src[this.pos] ?? '';
  }

  private eat(ch: string): boolean {
    this.skipWs();
    if (this.src[this.pos] === ch) { this.pos++; return true; }
    return false;
  }

  private expect(ch: string): void {
    if (!this.eat(ch)) throw new Error(`expected ${ch} at ${this.pos}`);
  }

  private name(): string {
    this.skipWs();
    const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(this.src.slice(this.pos));
    if (!m) throw new Error(`expected name at ${this.pos}`);
    this.pos += m[0].length;
    return m[0];
  }

  private value(): GqlValue {
    this.skipWs();
    const ch = this.src[this.pos] ?? '';
    if (ch === '$') {
      this.pos++;
      return { kind: 'var', name: this.name() };
    }
    if (ch === '"') {
      this.pos++;
      let out = '';
      while (this.pos < this.src.length && this.src[this.pos] !== '"') {
        if (this.src[this.pos] === '\\') {
          this.pos++;
          const esc = this.src[this.pos] ?? '';
          out += esc === 'n' ? '\n' : esc === 't' ? '\t' : esc === 'r' ? '\r' : esc;
          this.pos++;
        } else {
          out += this.src[this.pos];
          this.pos++;
        }
      }
      this.pos++;
      return { kind: 'string', value: out };
    }
    if (ch === '[') {
      this.pos++;
      const items: GqlValue[] = [];
      while (!this.eat(']')) {
        items.push(this.value());
        this.eat(',');
      }
      return { kind: 'list', items };
    }
    if (ch === '{') {
      this.pos++;
      const fields: Array<{ name: string; value: GqlValue }> = [];
      while (!this.eat('}')) {
        const n = this.name();
        this.expect(':');
        fields.push({ name: n, value: this.value() });
        this.eat(',');
      }
      return { kind: 'object', fields };
    }
    if (ch === '-' || /[0-9]/.test(ch)) {
      const m = /^-?[0-9]+(\.[0-9]+)?/.exec(this.src.slice(this.pos));
      if (!m) throw new Error('bad number');
      this.pos += m[0].length;
      return m[0].includes('.') ? { kind: 'float', value: Number(m[0]) } : { kind: 'int', value: Number(m[0]) };
    }
    const word = this.name();
    if (word === 'true') return { kind: 'bool', value: true };
    if (word === 'false') return { kind: 'bool', value: false };
    if (word === 'null') return { kind: 'null' };
    return { kind: 'enum', value: word };
  }

  private skipBalanced(open: string, close: string): void {
    this.skipWs();
    if (this.src[this.pos] !== open) return;
    let depth = 0;
    while (this.pos < this.src.length) {
      const ch = this.src[this.pos]!;
      if (ch === open) depth++;
      else if (ch === close) {
        depth--;
        this.pos++;
        if (depth === 0) return;
        continue;
      }
      this.pos++;
    }
  }

  private selectionSet(): GqlSel[] {
    this.expect('{');
    const out: GqlSel[] = [];
    for (;;) {
      this.skipWs();
      if (this.src[this.pos] === '}') { this.pos++; break; }
      if (this.src.startsWith('...', this.pos)) {
        this.pos += 3;
        this.skipWs();
        if (this.src.startsWith('on', this.pos) && !/[A-Za-z0-9_]/.test(this.src[this.pos + 2] ?? '')) {
          this.pos += 2;
          const type = this.name();
          const children = this.selectionSet();
          out.push({ alias: null, name: '', args: [], children, fragName: null, fragType: type });
        } else {
          const fragName = this.name();
          out.push({ alias: null, name: '', args: [], children: null, fragName, fragType: null });
        }
        continue;
      }
      let first = this.name();
      let alias: string | null = null;
      let fname = first;
      this.skipWs();
      if (this.src[this.pos] === ':') {
        this.pos++;
        alias = first;
        fname = this.name();
      }
      const args: Array<{ name: string; value: GqlValue }> = [];
      if (this.eat('(')) {
        for (;;) {
          this.skipWs();
          if (this.src[this.pos] === ')') { this.pos++; break; }
          const an = this.name();
          this.expect(':');
          args.push({ name: an, value: this.value() });
          this.eat(',');
        }
      }
      let children: GqlSel[] | null = null;
      this.skipWs();
      if (this.src[this.pos] === '{') children = this.selectionSet();
      out.push({ alias, name: fname, args, children, fragName: null, fragType: null });
    }
    return out;
  }

  parse(): { ops: GqlOp[]; fragments: Map<string, GqlSel[]> } {
    const ops: GqlOp[] = [];
    const fragments = new Map<string, GqlSel[]>();
    for (;;) {
      this.skipWs();
      if (this.pos >= this.src.length) break;
      if (this.src[this.pos] === '{') {
        ops.push({ type: 'query', name: null, selections: this.selectionSet() });
        continue;
      }
      const kw = this.name();
      if (kw === 'fragment') {
        const fname = this.name();
        this.name(); // 'on'
        this.name(); // type
        fragments.set(fname, this.selectionSet());
        continue;
      }
      if (kw !== 'query' && kw !== 'mutation' && kw !== 'subscription') throw new Error(`unknown operation ${kw}`);
      let opName: string | null = null;
      this.skipWs();
      if (this.src[this.pos] !== '(' && this.src[this.pos] !== '{') opName = this.name();
      if (this.src[this.pos] === '(') this.skipBalanced('(', ')');
      const selections = this.selectionSet();
      ops.push({ type: kw as 'query' | 'mutation', name: opName, selections });
    }
    return { ops, fragments };
  }
}

function gqlResolveValue(v: GqlValue, vars: Record<string, unknown>): unknown {
  switch (v.kind) {
    case 'var': return vars[v.name];
    case 'string': return v.value;
    case 'int': return v.value;
    case 'float': return v.value;
    case 'bool': return v.value;
    case 'null': return null;
    case 'enum': return v.value;
    case 'list': return v.items.map((i) => gqlResolveValue(i, vars));
    case 'object': {
      const o: Record<string, unknown> = {};
      for (const f of v.fields) o[f.name] = gqlResolveValue(f.value, vars);
      return o;
    }
  }
}

function gqlArg(sel: GqlSel, name: string, vars: Record<string, unknown>): unknown {
  const a = sel.args.find((x) => x.name === name);
  return a ? gqlResolveValue(a.value, vars) : undefined;
}

const INTROSPECTION: Record<string, { fields: string[]; enums: string[] }> = {
  Issue: { fields: ['id', 'number', 'title', 'state', 'body', 'url', 'createdAt', 'updatedAt', 'author', 'labels', 'comments'], enums: [] },
  PullRequest: { fields: ['id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'files', 'headRef', 'baseRef', 'author', 'createdAt', 'mergedAt', 'mergeCommit'], enums: [] },
  Repository: { fields: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'url', 'description', 'private', 'createdAt', 'updatedAt'], enums: [] },
  SearchType: { fields: [], enums: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'COMMIT'] },
  IssueState: { fields: [], enums: ['OPEN', 'CLOSED'] },
  MergeableState: { fields: [], enums: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
  PullRequestState: { fields: [], enums: ['OPEN', 'CLOSED', 'MERGED'] },
  OrderDirection: { fields: [], enums: ['ASC', 'DESC'] },
  IssueOrderField: { fields: [], enums: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] },
  RepositoryPermission: { fields: [], enums: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'] },
};

interface GqlCtx {
  vars: Record<string, unknown>;
  errors: Array<{ message: string }>;
  fragments: Map<string, GqlSel[]>;
}

function gqlErr(ctx: GqlCtx, msg: string): void {
  ctx.errors.push({ message: msg });
}

function gqlIssueFields(ctx: GqlCtx, repo: Repo, issue: Issue, sels: GqlSel[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const s of sels) {
    const key = s.alias ?? s.name;
    switch (s.name) {
      case 'id': out[key] = issue.gid; break;
      case 'number': out[key] = issue.number; break;
      case 'title': out[key] = issue.title; break;
      case 'state': out[key] = issue.state.toUpperCase(); break;
      case 'body': out[key] = issue.body; break;
      case 'url': out[key] = `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`; break;
      case '__typename': out[key] = 'Issue'; break;
      default: out[key] = null; gqlErr(ctx, `Cannot query field "${s.name}" on type "Issue".`); break;
    }
  }
  return out;
}

function gqlPullFields(ctx: GqlCtx, repo: Repo, pr: Pull, sels: GqlSel[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const s of sels) {
    const key = s.alias ?? s.name;
    switch (s.name) {
      case 'id': out[key] = pr.gid; break;
      case 'number': out[key] = pr.number; break;
      case 'title': out[key] = pr.title; break;
      case 'body': out[key] = pr.body; break;
      case 'state': out[key] = pr.merged ? 'MERGED' : pr.state.toUpperCase(); break;
      case 'merged': out[key] = pr.merged; break;
      case 'mergeable': out[key] = prMergeable(repo, pr); break;
      case 'headRefName': out[key] = pr.head; break;
      case 'baseRefName': out[key] = pr.base; break;
      case 'url': out[key] = `https://example.invalid/${repo.owner}/${repo.name}/pull/${pr.number}`; break;
      case 'mergedAt': out[key] = pr.mergedAt; break;
      case 'files': {
        const first = gqlArg(s, 'first', ctx.vars);
        const files = prFiles(repo, pr).map((f) => ({ path: f.filename }));
        const nodes = typeof first === 'number' ? files.slice(0, first) : files;
        out[key] = { nodes };
        break;
      }
      case '__typename': out[key] = 'PullRequest'; break;
      default: out[key] = null; gqlErr(ctx, `Cannot query field "${s.name}" on type "PullRequest".`); break;
    }
  }
  return out;
}

function gqlRepoFields(ctx: GqlCtx, repo: Repo, sels: GqlSel[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const s of sels) {
    const key = s.alias ?? s.name;
    switch (s.name) {
      case 'id': out[key] = gid('Repository', repo.dbId); break;
      case 'databaseId': out[key] = repo.dbId; break;
      case 'name': out[key] = repo.name; break;
      case 'nameWithOwner': out[key] = `${repo.owner}/${repo.name}`; break;
      case 'owner': out[key] = { login: repo.owner }; break;
      case 'defaultBranchRef': out[key] = { name: 'main' }; break;
      case 'viewerPermission': out[key] = 'ADMIN'; break;
      case 'hasIssuesEnabled': out[key] = true; break;
      case 'description': out[key] = repo.description; break;
      case 'url': out[key] = `https://example.invalid/${repo.owner}/${repo.name}`; break;
      case '__typename': out[key] = 'Repository'; break;
      case 'issue': {
        const num = gqlArg(s, 'number', ctx.vars);
        const issue = typeof num === 'number' ? repo.issues.get(num) : undefined;
        out[key] = issue && s.children ? gqlIssueFields(ctx, repo, issue, s.children) : issue ? { id: issue.gid, number: issue.number } : null;
        break;
      }
      case 'issues': {
        const first = gqlArg(s, 'first', ctx.vars);
        const after = gqlArg(s, 'after', ctx.vars);
        const states = gqlArg(s, 'states', ctx.vars);
        const orderBy = gqlArg(s, 'orderBy', ctx.vars) as { field?: string; direction?: string } | undefined;
        let list = [...repo.issues.values()];
        if (Array.isArray(states) && states.length) {
          const want = new Set(states.map((x) => String(x).toLowerCase()));
          list = list.filter((i) => want.has(i.state));
        }
        if (orderBy?.field === 'CREATED_AT' && orderBy?.direction === 'DESC') list.sort((a, b) => b.number - a.number || b.seq - a.seq);
        else if (orderBy?.field === 'CREATED_AT' && orderBy?.direction === 'ASC') list.sort((a, b) => a.number - b.number || a.seq - b.seq);
        else list.sort((a, b) => a.number - b.number);
        if (typeof after === 'string' && after !== '') {
          try {
            const decoded = Buffer.from(after, 'base64').toString('utf8');
            const m = /^cursor:(\d+)$/.exec(decoded);
            if (m) list = list.filter((i) => i.number > Number(m[1]));
          } catch { /* ignore bad cursor */ }
        }
        const total = list.length;
        const limited = typeof first === 'number' ? list.slice(0, first) : list;
        const nodes = s.children?.find((c) => c.name === 'nodes');
        const nodeSels = nodes?.children ?? [{ alias: null, name: 'number', args: [], children: null, fragName: null, fragType: null }];
        const endCursor = limited.length ? Buffer.from(`cursor:${limited[limited.length - 1]!.number}`, 'utf8').toString('base64') : null;
        const conn: Record<string, unknown> = {};
        for (const c of s.children ?? []) {
          if (c.name === 'nodes') conn[c.alias ?? 'nodes'] = limited.map((i) => gqlIssueFields(ctx, repo, i, nodeSels));
          else if (c.name === 'pageInfo') {
            conn[c.alias ?? 'pageInfo'] = { hasNextPage: limited.length < total, endCursor };
          } else if (c.name === 'totalCount') conn[c.alias ?? 'totalCount'] = total;
        }
        out[key] = conn;
        break;
      }
      case 'pullRequests': {
        const first = gqlArg(s, 'first', ctx.vars);
        let list = [...repo.pulls.values()].sort((a, b) => a.number - b.number);
        if (typeof first === 'number') list = list.slice(0, first);
        const nodes = s.children?.find((c) => c.name === 'nodes');
        const nodeSels = nodes?.children ?? [];
        const conn: Record<string, unknown> = {};
        for (const c of s.children ?? []) {
          if (c.name === 'nodes') conn[c.alias ?? 'nodes'] = list.map((p) => gqlPullFields(ctx, repo, p, nodeSels));
          else if (c.name === 'pageInfo') conn[c.alias ?? 'pageInfo'] = { hasNextPage: false, endCursor: null };
          else if (c.name === 'totalCount') conn[c.alias ?? 'totalCount'] = repo.pulls.size;
        }
        out[key] = conn;
        break;
      }
      case 'pullRequest': {
        const num = gqlArg(s, 'number', ctx.vars);
        const pr = typeof num === 'number' ? repo.pulls.get(num) : undefined;
        out[key] = pr && s.children ? gqlPullFields(ctx, repo, pr, s.children) : null;
        break;
      }
      default: out[key] = null; gqlErr(ctx, `Cannot query field "${s.name}" on type "Repository".`); break;
    }
  }
  return out;
}

function gqlExpand(sels: GqlSel[], ctx: GqlCtx, typeName: string): GqlSel[] {
  const out: GqlSel[] = [];
  for (const s of sels) {
    if (s.fragName) {
      const frag = ctx.fragments.get(s.fragName);
      if (frag) out.push(...gqlExpand(frag, ctx, typeName));
      continue;
    }
    if (s.fragType) {
      if (s.fragType === typeName && s.children) out.push(...gqlExpand(s.children, ctx, typeName));
      continue;
    }
    out.push(s);
  }
  return out;
}

function findRepoByGid(id: string): Repo | undefined {
  for (const repo of repos.values()) if (gid('Repository', repo.dbId) === id) return repo;
  return undefined;
}

function findIssueByGid(id: string): { repo: Repo; issue: Issue } | undefined {
  for (const repo of repos.values()) for (const issue of repo.issues.values()) if (issue.gid === id) return { repo, issue };
  return undefined;
}

function findPullByGid(id: string): { repo: Repo; pr: Pull } | undefined {
  for (const repo of repos.values()) for (const pr of repo.pulls.values()) if (pr.gid === id) return { repo, pr };
  return undefined;
}

function executeOperation(op: GqlOp, vars: Record<string, unknown>, fragments: Map<string, GqlSel[]>): { data: Record<string, unknown>; errors: Array<{ message: string }> } {
  const ctx: GqlCtx = { vars, errors: [], fragments };
  const data: Record<string, unknown> = {};
  const sels = gqlExpand(op.selections, ctx, op.type === 'query' ? 'Query' : 'Mutation');
  for (const s of sels) {
    const key = s.alias ?? s.name;
    if (op.type === 'query') {
      switch (s.name) {
        case 'viewer': {
          const inner = s.children ? gqlExpand(s.children, ctx, 'User') : [];
          const v: Record<string, unknown> = {};
          for (const c of inner) {
            if (c.name === 'login') v[c.alias ?? 'login'] = VIEWER_LOGIN;
            else if (c.name === '__typename') v[c.alias ?? '__typename'] = 'User';
            else { v[c.alias ?? c.name] = null; gqlErr(ctx, `Cannot query field "${c.name}" on type "Viewer".`); }
          }
          data[key] = v;
          break;
        }
        case 'repository': {
          const owner = gqlArg(s, 'owner', vars);
          const name = gqlArg(s, 'name', vars);
          const repo = typeof owner === 'string' && typeof name === 'string' ? lookupRepo(owner, name) : undefined;
          data[key] = repo && s.children ? gqlRepoFields(ctx, repo, gqlExpand(s.children, ctx, 'Repository')) : null;
          break;
        }
        case 'node': {
          const id = gqlArg(s, 'id', vars);
          let node: Record<string, unknown> | null = null;
          if (typeof id === 'string') {
            const repo = findRepoByGid(id);
            if (repo) {
              node = { id: gid('Repository', repo.dbId) };
              const inner = s.children ? gqlExpand(s.children, ctx, 'Repository') : [];
              for (const c of inner) {
                if (c.fragType) continue;
                if (c.name === 'name') node[c.alias ?? 'name'] = repo.name;
                else if (c.name === 'nameWithOwner') node[c.alias ?? 'nameWithOwner'] = `${repo.owner}/${repo.name}`;
                else if (c.name === 'id') node[c.alias ?? 'id'] = gid('Repository', repo.dbId);
              }
              // inline fragments on Repository
              for (const c of s.children ?? []) {
                if (c.fragType === 'Repository' && c.children) {
                  for (const f of gqlExpand(c.children, ctx, 'Repository')) {
                    if (f.name === 'name') node[f.alias ?? 'name'] = repo.name;
                    else if (f.name === 'nameWithOwner') node[f.alias ?? 'nameWithOwner'] = `${repo.owner}/${repo.name}`;
                    else if (f.name === 'id') node[f.alias ?? 'id'] = gid('Repository', repo.dbId);
                  }
                }
              }
            }
          }
          data[key] = node;
          break;
        }
        case '__type': {
          const typeName = gqlArg(s, 'name', vars);
          const info = typeof typeName === 'string' ? INTROSPECTION[typeName] : undefined;
          if (!info) { data[key] = null; break; }
          const inner: Record<string, unknown> = { name: typeName };
          for (const c of s.children ?? []) {
            if (c.name === 'fields') inner[c.alias ?? 'fields'] = info.fields.map((f) => ({ name: f }));
            else if (c.name === 'enumValues') inner[c.alias ?? 'enumValues'] = info.enums.map((e) => ({ name: e }));
            else if (c.name === 'name') inner[c.alias ?? 'name'] = typeName;
          }
          data[key] = inner;
          break;
        }
        case '__typename': data[key] = 'Query'; break;
        default: data[key] = null; gqlErr(ctx, `Cannot query field "${s.name}" on type "Query".`); break;
      }
    } else {
      // mutation
      switch (s.name) {
        case 'createIssue': {
          const input = gqlArg(s, 'input', vars) as { repositoryId?: string; title?: string; body?: string } | undefined;
          const repo = input?.repositoryId ? findRepoByGid(input.repositoryId) : undefined;
          let issue: Issue | undefined;
          if (repo && input?.title) {
            const created = createIssueIn(repo, input.title, input.body ?? '', []);
            if (!('error' in created)) issue = created;
          }
          const inner: Record<string, unknown> = {};
          for (const c of s.children ?? []) {
            if (c.name === 'issue' && issue) inner[c.alias ?? 'issue'] = gqlIssueFields(ctx, repo!, issue, c.children ?? []);
            else if (c.name === 'issue') inner[c.alias ?? 'issue'] = null;
          }
          data[key] = inner;
          break;
        }
        case 'closeIssue': {
          const input = gqlArg(s, 'input', vars) as { issueId?: string } | undefined;
          const found = input?.issueId ? findIssueByGid(input.issueId) : undefined;
          if (found) found.issue.state = 'closed';
          const inner: Record<string, unknown> = {};
          for (const c of s.children ?? []) {
            if (c.name === 'issue' && found) inner[c.alias ?? 'issue'] = gqlIssueFields(ctx, found.repo, found.issue, c.children ?? []);
            else if (c.name === 'issue') inner[c.alias ?? 'issue'] = null;
          }
          data[key] = inner;
          break;
        }
        case 'createPullRequest': {
          const input = gqlArg(s, 'input', vars) as { repositoryId?: string; baseRefName?: string; headRefName?: string; title?: string; body?: string } | undefined;
          const repo = input?.repositoryId ? findRepoByGid(input.repositoryId) : undefined;
          let pr: Pull | undefined;
          if (repo && input?.headRefName && input?.baseRefName && input?.title) {
            const created = createPullIn(repo, input.title, input.body ?? '', input.headRefName, input.baseRefName);
            if (!('error' in created)) pr = created;
          }
          const inner: Record<string, unknown> = {};
          for (const c of s.children ?? []) {
            if (c.name === 'pullRequest' && pr) inner[c.alias ?? 'pullRequest'] = gqlPullFields(ctx, repo!, pr, c.children ?? []);
            else if (c.name === 'pullRequest') inner[c.alias ?? 'pullRequest'] = null;
          }
          data[key] = inner;
          break;
        }
        case 'mergePullRequest': {
          const input = gqlArg(s, 'input', vars) as { pullRequestId?: string; mergeMethod?: string } | undefined;
          const found = input?.pullRequestId ? findPullByGid(input.pullRequestId) : undefined;
          if (found && found.pr.state === 'open') doMerge(found.repo, found.pr);
          const inner: Record<string, unknown> = {};
          for (const c of s.children ?? []) {
            if (c.name === 'pullRequest' && found) inner[c.alias ?? 'pullRequest'] = gqlPullFields(ctx, found.repo, found.pr, c.children ?? []);
            else if (c.name === 'pullRequest') inner[c.alias ?? 'pullRequest'] = null;
          }
          data[key] = inner;
          break;
        }
        case 'addComment': {
          const input = gqlArg(s, 'input', vars) as { subjectId?: string; body?: string } | undefined;
          const found = input?.subjectId ? findIssueByGid(input.subjectId) : undefined;
          let comment: Comment | undefined;
          if (found && input?.body !== undefined) {
            const id = found.repo.nextComment++;
            comment = { id, gid: gid('IssueComment', found.repo.dbId, found.issue.number, id), body: input.body };
            found.issue.comments.push(comment);
          }
          const inner: Record<string, unknown> = {};
          for (const c of s.children ?? []) {
            if (c.name === 'commentEdge') {
              const edge: Record<string, unknown> = {};
              for (const n of c.children ?? []) {
                if (n.name === 'node' && comment) edge[n.alias ?? 'node'] = { id: comment.gid, body: comment.body };
                else if (n.name === 'node') edge[n.alias ?? 'node'] = null;
              }
              inner[c.alias ?? 'commentEdge'] = edge;
            }
          }
          data[key] = inner;
          break;
        }
        default: data[key] = null; gqlErr(ctx, `Cannot query field "${s.name}" on type "Mutation".`); break;
      }
    }
  }
  return { data, errors: ctx.errors };
}

async function handleGraphQL(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!authOk(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  const bodyBuf = await readBody(req);
  const parsed = parseJsonBody(bodyBuf);
  if (!parsed.ok) {
    sendJson(res, 400, { message: 'Problems parsing JSON' });
    return;
  }
  const runOne = (op: unknown): Record<string, unknown> => {
    const rec = asRecord(op);
    const query = typeof rec.query === 'string' ? rec.query : '';
    const vars = asRecord(rec.variables);
    const operationName = typeof rec.operationName === 'string' ? rec.operationName : undefined;
    try {
      const { ops, fragments } = new GqlParser(query).parse();
      let chosen = ops[0];
      if (operationName) {
        const found = ops.find((o) => o.name === operationName);
        if (found) chosen = found;
      }
      if (!chosen) return { data: null, errors: [{ message: 'No operation provided' }] };
      const { data, errors } = executeOperation(chosen, vars, fragments);
      return errors.length ? { data, errors } : { data };
    } catch (err) {
      return { data: null, errors: [{ message: err instanceof Error ? err.message : String(err) }] };
    }
  };
  if (Array.isArray(parsed.value)) {
    sendJson(res, 200, parsed.value.map(runOne));
    return;
  }
  sendJson(res, 200, runOne(parsed.value));
}

// ---------------------------------------------------------------------------
// MCP (JSON-RPC 2.0, Streamable HTTP, revision 2026-07-28)
// ---------------------------------------------------------------------------

const MCP_TOOLS: Array<Record<string, unknown>> = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, description: { type: 'string', description: 'Repository description' }, private: { type: 'boolean', description: 'Whether the repository is private' } }, required: ['name'] },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Issue title' }, body: { type: 'string', description: 'Issue body' } }, required: ['owner', 'repo', 'title'] },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, state: { type: 'string', description: 'Issue state: open, closed or all' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Pull request title' }, body: { type: 'string', description: 'Pull request body' }, head: { type: 'string', description: 'Head branch name' }, base: { type: 'string', description: 'Base branch name' } }, required: ['owner', 'repo', 'title', 'head', 'base'] },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request by number.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, pull_number: { type: 'number', description: 'Pull request number' } }, required: ['owner', 'repo', 'pull_number'] },
  },
];

function mcpToolResult(obj: unknown): Record<string, unknown> {
  const text = typeof obj === 'string' ? obj : JSON.stringify(obj);
  return { content: [{ type: 'text', text }], structuredContent: obj };
}

function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function mcpCall(name: string, args: Record<string, unknown>): { result: Record<string, unknown> } | { rpcError: { code: number; message: string } } {
  const get = (k: string): unknown => args[k];
  const str = (k: string): string | undefined => (typeof args[k] === 'string' ? (args[k] as string) : undefined);
  switch (name) {
    case 'create_repo': {
      const repoName = str('name');
      if (!repoName) return { result: mcpToolError('Missing required argument: name') };
      if (repos.has(repoName)) return { result: mcpToolError(`Repository ${repoName} already exists`) };
      const repo: Repo = {
        name: repoName, owner: VIEWER_LOGIN,
        description: str('description') ?? '',
        priv: args.private === true,
        dbId: nextDbId++, seq: seqCounter++,
        refs: new Map(), issues: new Map(), pulls: new Map(), labels: new Map(),
        nextNum: 1, nextComment: 1,
      };
      repos.set(repoName, repo);
      return { result: mcpToolResult(repoObject(repo)) };
    }
    case 'get_repo': {
      const owner = str('owner');
      const repoName = str('repo');
      if (!owner || !repoName) return { result: mcpToolError('Missing required argument: owner or repo') };
      const repo = lookupRepo(owner, repoName);
      if (!repo) return { result: mcpToolError(`Repository ${owner}/${repoName} not found`) };
      return { result: mcpToolResult(repoObject(repo)) };
    }
    case 'create_issue': {
      const owner = str('owner');
      const repoName = str('repo');
      const title = str('title');
      if (!owner || !repoName || !title) return { result: mcpToolError('Missing required argument: owner, repo or title') };
      const repo = lookupRepo(owner, repoName);
      if (!repo) return { result: mcpToolError(`Repository ${owner}/${repoName} not found`) };
      const created = createIssueIn(repo, title, str('body') ?? '', []);
      if ('error' in created) return { result: mcpToolError(created.error) };
      return { result: mcpToolResult(issueObject(repo, created)) };
    }
    case 'list_issues': {
      const owner = str('owner');
      const repoName = str('repo');
      if (!owner || !repoName) return { result: mcpToolError('Missing required argument: owner or repo') };
      const repo = lookupRepo(owner, repoName);
      if (!repo) return { result: mcpToolError(`Repository ${owner}/${repoName} not found`) };
      const state = str('state') ?? 'open';
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((i) => i.state === state);
      list.sort((a, b) => a.number - b.number);
      return { result: mcpToolResult(list.map((i) => issueObject(repo, i))) };
    }
    case 'create_pull_request': {
      const owner = str('owner');
      const repoName = str('repo');
      const title = str('title');
      const head = str('head');
      const base = str('base');
      if (!owner || !repoName || !title || !head || !base) return { result: mcpToolError('Missing required argument: owner, repo, title, head or base') };
      const repo = lookupRepo(owner, repoName);
      if (!repo) return { result: mcpToolError(`Repository ${owner}/${repoName} not found`) };
      const created = createPullIn(repo, title, str('body') ?? '', head, base);
      if ('error' in created) return { result: mcpToolError(created.error) };
      return { result: mcpToolResult(pullObject(repo, created)) };
    }
    case 'merge_pull_request': {
      const owner = str('owner');
      const repoName = str('repo');
      const num = get('pull_number');
      if (!owner || !repoName || typeof num !== 'number') return { result: mcpToolError('Missing required argument: owner, repo or pull_number') };
      const repo = lookupRepo(owner, repoName);
      if (!repo) return { result: mcpToolError(`Repository ${owner}/${repoName} not found`) };
      const pr = repo.pulls.get(num);
      if (!pr) return { result: mcpToolError(`Pull request #${num} not found`) };
      const merged = doMerge(repo, pr);
      if ('error' in merged) return { result: mcpToolError(merged.error) };
      return { result: mcpToolResult({ number: pr.number, sha: merged.sha, merged: true, state: 'closed', message: `Pull Request #${num} merged` }) };
    }
    default:
      return { rpcError: { code: -32602, message: `Unknown tool: ${name}` } };
  }
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const method = req.method ?? 'POST';
  if (method === 'DELETE' || method === 'GET') {
    sendJson(res, 200, {});
    return;
  }
  if (method !== 'POST') {
    sendJson(res, 405, { message: 'Method Not Allowed' });
    return;
  }
  const bodyBuf = await readBody(req);
  // Auth is decided before parsing: a call with no Authorization header is 401.
  if (!authOk(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  const parsed = parseJsonBody(bodyBuf);
  if (!parsed.ok) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  const rec = asRecord(parsed.value);
  const id = rec.id === undefined ? null : (rec.id as string | number | null);
  const rpcMethod = typeof rec.method === 'string' ? rec.method : '';
  const params = asRecord(rec.params);
  const ok = (result: unknown): void => sendJson(res, 200, { jsonrpc: '2.0', id, result });
  const err = (code: number, message: string): void => sendJson(res, 200, { jsonrpc: '2.0', id, error: { code, message } });
  if (rpcMethod === 'server/discover') {
    ok({
      resultType: 'DiscoverResult',
      supportedVersions: ['2026-07-28'],
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: '1.0.0' },
      _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'forge', version: '1.0.0' } },
    });
    return;
  }
  if (rpcMethod === 'initialize') {
    const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25';
    const negotiated = ['2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05', '2026-07-28'].includes(requested) ? requested : '2025-11-25';
    ok({
      protocolVersion: negotiated,
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: '1.0.0' },
    });
    return;
  }
  if (rpcMethod === 'notifications/initialized' || rpcMethod.startsWith('notifications/')) {
    sendJson(res, 202, {});
    return;
  }
  if (rpcMethod === 'tools/list') {
    ok({ tools: MCP_TOOLS });
    return;
  }
  if (rpcMethod === 'tools/call') {
    const toolName = typeof params.name === 'string' ? params.name : '';
    const args = asRecord(params.arguments);
    const outcome = mcpCall(toolName, args);
    if ('rpcError' in outcome) { err(outcome.rpcError.code, outcome.rpcError.message); return; }
    ok(outcome.result);
    return;
  }
  if (rpcMethod === 'ping') {
    ok({});
    return;
  }
  err(-32601, `Method not found: ${rpcMethod}`);
}

// ---------------------------------------------------------------------------
// router
// ---------------------------------------------------------------------------

export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      try {
        const { path } = parseQuery(req);
        const method = req.method ?? 'GET';
        if (method === 'GET' && path === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }
        const gitMatch = /^\/([^/]+)\/([^/]+)\.git(\/.*)?$/.exec(path);
        if (gitMatch) {
          const owner = decodeURIComponent(gitMatch[1]!);
          const repoName = decodeURIComponent(gitMatch[2]!);
          const sub = gitMatch[3] ?? '';
          const repo = lookupRepo(owner, repoName);
          if (sub === '/info/refs' && method === 'GET') {
            const service = parseQuery(req).query.get('service');
            if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
              sendJson(res, 404, { message: 'Not Found' });
              return;
            }
            handleInfoRefs(repo, service, req, res);
            return;
          }
          if (!repo) {
            sendJson(res, 404, { message: 'Not Found' });
            return;
          }
          if (sub === '/git-upload-pack' && method === 'POST') {
            const body = await readBody(req);
            handleUploadPack(repo, req, res, body);
            return;
          }
          if (sub === '/git-receive-pack' && method === 'POST') {
            const body = await readBody(req);
            handleReceivePack(repo, req, res, body);
            return;
          }
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        if (path === '/api/graphql' && method === 'POST') {
          await handleGraphQL(req, res);
          return;
        }
        if (path === '/mcp') {
          await handleMcp(req, res);
          return;
        }
        if (path === '/api/v3' || path.startsWith('/api/v3/')) {
          await handleRest(req, res);
          return;
        }
        sendJson(res, 404, { message: 'Not Found' });
      } catch (err) {
        try {
          sendJson(res, 500, { message: err instanceof Error ? err.message : String(err) });
        } catch {
          try { res.end(); } catch { /* closed */ }
        }
      }
    })();
  });
}
