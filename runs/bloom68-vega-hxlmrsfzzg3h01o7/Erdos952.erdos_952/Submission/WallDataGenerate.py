#!/usr/bin/env python3
"""Losslessly encode the existing black-wall certificate in new WallData files.

External hashes and arithmetic checks here are provenance/sanity checks only.
Lean's Boolean checker and its soundness theorem establish every path claim.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEST = ROOT / 'Submission'
INPUT = ROOT / 'sieve_d2'
START = (146, -149)
FINISH = (576956, 95986)
EDGES = 1812223
RAW_SHA256 = '96754f307803aa9fc8eac8990d47fb572ee18ef8887eab2c3936f51e1ba4e272'
GZIP_SHA256 = '83cdf74e3a88aa19e40b41d80cc20861233f70ac3ae0889ffed1e949b4fecef9'
STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
COEFFS = [None, (-1, -3, 5), (3, 1, 5), (6, 4, 13), (-4, -6, 13),
          (-3, -5, 17), (5, 3, 17), (13, 11, 29), (-11, -13, 29), (-5, -7, 37)]


def write_if_changed(path, text):
    # Preserve timestamps and avoid racing readers on deterministic regeneration.
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def load_data():
    meta = json.loads((INPUT / 'black_wall.json').read_text())
    compressed = (INPUT / 'black_wall.bin.gz').read_bytes()
    raw = gzip.decompress(compressed)
    assert hashlib.sha256(compressed).hexdigest() == meta['compressed_sha256'] == GZIP_SHA256
    assert hashlib.sha256(raw).hexdigest() == meta['raw_sha256'] == RAW_SHA256
    assert meta['edges'] == EDGES and tuple(meta['start']) == START
    assert len(raw) == EDGES + 1
    assert meta['directions'][:4] == [list(d) for d in STEPS]
    assert tuple(a + b for a, b in zip(meta['start'], meta['winding'])) == FINISH
    return raw


def black(x, y, label):
    if label == 0:
        return (1 + x - y) % 3 == 0 and (x + y) % 3 == 0
    a, b, m = COEFFS[label]
    return (1 + a * x + b * y) % m == 0


def ascii_data(raw):
    assert all(b >> 3 < 10 and b & 7 < 4 for b in raw)
    text = ''.join(chr(48 + (b >> 3) * 4 + (b & 7)) for b in raw)
    # Require a byte-for-byte inverse, including the unused last direction.
    back = bytes((((ord(c) - 48) // 4) << 3) | ((ord(c) - 48) % 4) for c in text)
    assert back == raw
    return text


def packed_words(raw, word_size=64):
    assert word_size > 0
    codes = [(b >> 3) * 4 + (b & 7) for b in raw]
    assert all(b >> 3 < 10 and b & 7 < 4 for b in raw)
    words = []
    for i in range(0, len(codes), word_size):
        word = 1
        for c in reversed(codes[i:i+word_size]):
            word = 40 * word + c
        words.append(word)
    decoded = []
    for word in words:
        while word != 1:
            assert word >= 40
            decoded.append(word % 40)
            word //= 40
    assert decoded == codes
    back = bytes(((c // 4) << 3) | (c % 4) for c in decoded)
    assert back == raw
    return words


def lean_nat_list(words):
    return '[\n' + ',\n'.join('  ' + str(w) for w in words) + ']'


def coords(p):
    return f'⟨{p[0]}, {p[1]}⟩'


def benchmark(raw, offset, n, encoding="ascii", word_size=64):
    assert 0 <= offset <= EDGES and 0 <= n <= EDGES - offset
    p = START
    for b in raw[:offset]:
        dx, dy = STEPS[b & 7]
        p = p[0] + dx, p[1] + dy
    q = p
    for b in raw[offset:offset+n]:
        assert black(*q, b >> 3)
        dx, dy = STEPS[b & 7]
        q = q[0] + dx, q[1] + dy
    assert black(*q, raw[offset+n] >> 3)
    segment = raw[offset:offset+n+1]
    if encoding == 'ascii':
        data = '"' + ascii_data(segment) + '"'
        typ = 'String'
        module = 'WallDataChecker'
        prefix = ''
        check = f'checkChunk {n} data {coords(p)} {coords(q)}'
        proof = 'checkChunk_sound accepted'
    else:
        values = (packed_words(segment, word_size) if encoding == 'packed'
                  else [(b >> 3) * 4 + (b & 7) for b in segment])
        data = lean_nat_list(values)
        typ = 'List ℕ'
        prefix = 'Packed' if encoding == 'packed' else 'List'
        module = 'WallDataPackedChecker' if encoding == 'packed' else 'WallDataListChecker'
        checker = 'checkPacked' if encoding == 'packed' else 'checkCodes'
        check = f'{checker} {coords(q)} {n} data {coords(p)}'
        proof = f'{checker}_sound _ _ _ _ accepted'
    suffix = f'{offset}_{n}' + (f'_{word_size}' if encoding == 'packed' else '')
    name = f'WallData{prefix}Bench{suffix}'
    ns = f'{prefix}Bench{suffix}'
    src = f'''import Submission.{module}

-- Exact raw vertices {offset} through {offset+n}, inclusive.
namespace Erdos952.WallData.{ns}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def data : {typ} := {data}

theorem accepted : {check} = true := by
  decide +kernel

theorem path : BlackPath {n} {coords(p)} {coords(q)} :=
  {proof}

#print axioms accepted
#print axioms path
#check path
end Erdos952.WallData.{ns}
'''
    path = DEST / (name + '.lean')
    write_if_changed(path, src)
    print(json.dumps({'source': str(path.relative_to(ROOT)), 'edges': n,
                      'offset': offset, 'start': p, 'finish': q, 'encoding': encoding}))



def append_tree(names):
    assert names
    if len(names) == 1:
        return names[0]
    k = len(names) // 2
    return f'({append_tree(names[:k])}).append ({append_tree(names[k:])})'


def generate_full(raw, chunk_edges=4096, word_size=64, chunks_per_file=16):
    assert chunk_edges > 0 and word_size > 0 and chunks_per_file > 0
    chunks = []
    position = START
    recovered_hash = hashlib.sha256()
    for offset in range(0, EDGES, chunk_edges):
        n = min(chunk_edges, EDGES - offset)
        start = position
        for i in range(offset, offset+n):
            b = raw[i]
            label, direction = b >> 3, b & 7
            assert label < 10 and direction < 4
            assert black(*position, label), (i, position, label)
            dx, dy = STEPS[direction]
            position = position[0] + dx, position[1] + dy
        assert black(*position, raw[offset+n] >> 3)
        segment = raw[offset:offset+n+1]
        words = packed_words(segment, word_size)
        recovered_hash.update(segment[:-1])
        chunks.append({'index': len(chunks), 'offset': offset, 'edges': n,
                       'start': start, 'finish': position, 'words': words,
                       'raw_sha256': hashlib.sha256(segment).hexdigest()})
    recovered_hash.update(raw[-1:])
    assert position == FINISH
    assert recovered_hash.hexdigest() == RAW_SHA256
    assert sum(c['edges'] for c in chunks) == EDGES
    parts = []
    for pi, base in enumerate(range(0, len(chunks), chunks_per_file)):
        group = chunks[base:base+chunks_per_file]
        module = f'WallDataPart{pi:02d}'
        namespace = f'Erdos952.WallData.Part{pi:02d}'
        out = ['import Submission.WallDataPackedChecker', '', '/-!',
               '# Exact black-wall certificate chunks', '',
               'Generated by `python3 Submission/WallDataGenerate.py full`.',
               f'Raw SHA-256: {RAW_SHA256}.',
               f'Each data list packs {word_size} or fewer codes per base-forty word, with sentinel 1.',
               'Every endpoint and every blackness label below is checked by the Lean kernel.',
               '-/', '', f'namespace {namespace}',
               'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
               'set_option Elab.async false', '']
        names = []
        for c in group:
            tag = f"{c['index']:04d}"
            c['module'] = module
            c['data_name'] = f'{namespace}.data{tag}'
            c['path_name'] = f'{namespace}.path{tag}'
            out += [f"-- Raw vertex offsets {c['offset']} through {c['offset']+c['edges']} inclusive.",
                    f'def data{tag} : List ℕ := {lean_nat_list(c["words"])}', '',
                    f'theorem accepted{tag} :',
                    f'    checkPacked {coords(c["finish"])} {c["edges"]} data{tag} {coords(c["start"])} = true := by',
                    '  decide +kernel', '',
                    f'theorem path{tag} : BlackPath {c["edges"]} {coords(c["start"])} {coords(c["finish"])} :=',
                    f'  checkPacked_sound _ _ _ _ accepted{tag}', '']
            names.append(f'path{tag}')
        total = sum(c['edges'] for c in group)
        out += [f'/-- The exact contiguous subpath in this module: {total} edges. -/',
                f'theorem path : BlackPath {total} {coords(group[0]["start"])} {coords(group[-1]["finish"])} :=',
                '  ' + append_tree(names), '', f'end {namespace}', '']
        path = DEST / (module + '.lean')
        write_if_changed(path, '\n'.join(out))
        parts.append({'module': module, 'source': str(path.relative_to(ROOT)),
                      'edges': total, 'first_chunk': base, 'chunk_count': len(group),
                      'start': group[0]['start'], 'finish': group[-1]['finish'],
                      'path_name': namespace + '.path'})
    imports = '\n'.join('import Submission.' + p['module'] for p in parts)
    expression = append_tree([f'Part{pi:02d}.path' for pi in range(len(parts))])
    final = f'''{imports}

/-!
# Kernel-certified finite black wall in the w lattice

This is ONLY a certificate for the supplied finite path. It is not an arbitrary-D
obstruction, a Gaussian-prime path, or a solution of the Gaussian moat problem.
No existing Submission module, in particular Spec, is imported or modified.

The 1,812,224 original vertex bytes are encoded losslessly in {len(chunks)} chunks,
with one overlapping vertex between consecutive chunks. Each chunk is accepted
by `decide +kernel`; exact-length path proofs are concatenated at checked endpoints.
-/

namespace Erdos952.WallData

/-- Initial vertex in w coordinates. -/
def start : GaussianInt := ⟨146, -149⟩

/-- Final vertex in w coordinates. -/
def finish : GaussianInt := ⟨576956, 95986⟩

/-- All 1,812,223 edges of the supplied path, with both endpoints black. -/
theorem wall_path_exact : BlackPath 1812223 start finish :=
  {expression}

/-- The requested black nearest-neighbor reachability statement. -/
theorem wall_path :
    Relation.ReflTransGen
      (fun p q : GaussianInt => Black p ∧ Black q ∧ (q - p).norm = 1)
      start finish :=
  wall_path_exact.toRTC

theorem start_black : Black start := wall_path_exact.black_start

theorem finish_black : Black finish := wall_path_exact.black_end

/-- The winding displacement recorded in the original metadata. -/
theorem wall_displacement : finish - start = (⟨576810, 96135⟩ : GaussianInt) := by
  decide +kernel

end Erdos952.WallData
'''
    write_if_changed(DEST / 'WallData.lean', final)
    manifest = {
        'format': 'WallData-base40-sentinel-v1',
        'input': 'sieve_d2/black_wall.bin.gz', 'raw_sha256': RAW_SHA256,
        'compressed_sha256': GZIP_SHA256, 'raw_vertices': len(raw), 'edges': EDGES,
        'start': START, 'finish': FINISH, 'chunk_edges': chunk_edges,
        'word_codes': word_size, 'chunks_per_file': chunks_per_file,
        'chunk_count': len(chunks), 'part_count': len(parts),
        'encoded_vertex_codes_including_overlaps': sum(c['edges']+1 for c in chunks),
        'word_count': sum(len(c['words']) for c in chunks),
        'chunks': [{k: v for k, v in c.items() if k != 'words'} for c in chunks],
        'parts': parts, 'final_source': 'Submission/WallData.lean',
    }
    write_if_changed(DEST / 'WallDataManifest.json', json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({k: v for k, v in manifest.items() if k not in ('chunks', 'parts')}))



def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    b = sub.add_parser('bench')
    b.add_argument('--edges', type=int, default=64)
    b.add_argument('--offset', type=int, default=0)
    b.add_argument('--encoding', choices=['ascii', 'codes', 'packed'], default='ascii')
    b.add_argument('--word-size', type=int, default=64)
    f = sub.add_parser('full')
    f.add_argument('--chunk-edges', type=int, default=4096)
    f.add_argument('--word-size', type=int, default=64)
    f.add_argument('--chunks-per-file', type=int, default=16)
    args = p.parse_args()
    raw = load_data()
    if args.command == 'bench':
        benchmark(raw, args.offset, args.edges, args.encoding, args.word_size)
    elif args.command == 'full':
        generate_full(raw, args.chunk_edges, args.word_size, args.chunks_per_file)

if __name__ == '__main__':
    main()
