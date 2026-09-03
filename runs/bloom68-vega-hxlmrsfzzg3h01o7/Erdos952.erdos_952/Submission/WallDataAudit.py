#!/usr/bin/env python3
"""Independently recover raw bytes from generated WallData Lean source files.

This is a provenance audit, not a replacement for the Lean kernel proofs.
Does not import or call WallDataGenerate.py and does not use a position table.
"""
from pathlib import Path
import gzip
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent.parent
SUB = ROOT / 'Submission'


def decode(words):
    out = bytearray()
    for word in words:
        assert word >= 40, ('empty word', word)
        while word != 1:
            assert word >= 40, ('invalid sentinel', word)
            word, code = divmod(word, 40)
            label, direction = divmod(code, 4)
            out.append((label << 3) | direction)
    return bytes(out)


def main():
    manifest = json.loads((SUB / 'WallDataManifest.json').read_text())
    meta = json.loads((ROOT / 'sieve_d2/black_wall.json').read_text())
    original = gzip.decompress((ROOT / 'sieve_d2/black_wall.bin.gz').read_bytes())
    chunks = {}
    source_hashes = {}
    for part in manifest['parts']:
        file = ROOT / part['source']
        text = file.read_text()
        source_hashes[part['source']] = hashlib.sha256(file.read_bytes()).hexdigest()
        matches = re.findall(r'def data(\d{4}) : List ℕ := \[([\d,\s]+)\]', text)
        assert len(matches) == part['chunk_count']
        for tag, numbers in matches:
            index = int(tag)
            words = [int(n) for n in numbers.split(',')]
            assert index not in chunks
            chunks[index] = decode(words)
            entry = manifest['chunks'][index]
            p, q, n = entry['start'], entry['finish'], entry['edges']
            expected = (f'checkPacked ⟨{q[0]}, {q[1]}⟩ {n} data{tag} '
                        f'⟨{p[0]}, {p[1]}⟩ = true := by\n  decide +kernel')
            assert expected in text
            assert hashlib.sha256(chunks[index]).hexdigest() == entry['raw_sha256']
            assert len(chunks[index]) == n + 1
            assert chunks[index] == original[entry['offset']:entry['offset']+n+1]
    assert sorted(chunks) == list(range(manifest['chunk_count']))
    recovered = bytearray()
    prev = None
    edges = 0
    position = tuple(meta['start'])
    tests = [lambda x,y: (1+x-y)%3 == 0 and (x+y)%3 == 0,
             lambda x,y: (1-x-3*y)%5 == 0,
             lambda x,y: (1+3*x+y)%5 == 0,
             lambda x,y: (1+6*x+4*y)%13 == 0,
             lambda x,y: (1-4*x-6*y)%13 == 0,
             lambda x,y: (1-3*x-5*y)%17 == 0,
             lambda x,y: (1+5*x+3*y)%17 == 0,
             lambda x,y: (1+13*x+11*y)%29 == 0,
             lambda x,y: (1-11*x-13*y)%29 == 0,
             lambda x,y: (1-5*x-7*y)%37 == 0]
    for index in sorted(chunks):
        data = chunks[index]
        entry = manifest['chunks'][index]
        assert entry['offset'] == edges
        assert tuple(entry['start']) == position
        if prev is not None:
            assert prev[-1] == data[0]
        for b in data[:-1]:
            label, direction = b >> 3, b & 7
            assert 0 <= label < 10 and 0 <= direction < 4
            assert tests[label](*position)
            dx, dy = [(1,0), (0,1), (-1,0), (0,-1)][direction]
            position = position[0] + dx, position[1] + dy
        assert tests[data[-1] >> 3](*position)
        assert tuple(entry['finish']) == position
        recovered.extend(data[:-1])
        edges += len(data) - 1
        prev = data
    recovered.extend(prev[-1:])
    assert bytes(recovered) == original
    assert edges == manifest['edges'] == meta['edges'] == 1812223
    assert len(recovered) == 1812224
    assert position == tuple(manifest['finish']) == (576956, 95986)
    assert recovered[-1] & 7 == 0
    digest = hashlib.sha256(recovered).hexdigest()
    assert digest == meta['raw_sha256'] == manifest['raw_sha256']
    result = {'provenance_audit': 'PASS (external, not a Lean proof)',
              'recovered_raw_bytes': len(recovered), 'raw_sha256': digest,
              'edges': edges, 'chunks': len(chunks), 'parts': len(manifest['parts']),
              'start': meta['start'], 'finish': position,
              'last_dummy_direction': recovered[-1] & 7,
              'all_source_words_decoded': True, 'all_overlaps_equal': True,
              'all_labels_externally_rechecked': True, 'source_sha256': source_hashes}
    (SUB / 'WallDataAudit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'source_sha256'}, indent=2))

if __name__ == '__main__':
    main()
