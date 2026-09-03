#!/usr/bin/env python3
"""Reproducible positive/negative regression tests. No q=17 tag search is run.

Tests solver root arithmetic/brute force, Python/native checker agreement,
malformed-tree rejection even after updating the hash, and a weak-only labeling
that must fail the repeated-triple test. The weak labeling is NOT a B3 result.
"""
from __future__ import annotations
import gzip
import itertools
import json
from pathlib import Path
import subprocess
import tempfile

import singer_half_tag_coherence as audit
import singer_half_tag_verify as verify


def main():
    tests = {"solver_self_test": audit.compile_solver(), "q17_tag_searches": 0}
    data = json.loads((audit.OUT/"q11_three_deletions.json").read_text())
    agreement = []
    for index in (0, 17, 219):
        record = data["instances"][index]
        T, rows, _ = verify.reconstruct(data["construction"], record)
        raw = gzip.decompress((audit.OUT/record["proof"]).read_bytes())
        python_answer = verify.check_tree(len(T), 5, rows, record)
        native_answer = verify.fast_tree(len(T), 5, rows, record, raw)
        assert python_answer == native_answer
        agreement.append(record["deleted_indices"])
    tests["independent_checker_backend_agreement"] = agreement

    record = data["instances"][0]
    T, rows, _ = verify.reconstruct(data["construction"], record)
    raw = gzip.decompress((audit.OUT/record["proof"]).read_bytes())
    header, *tokens = raw.splitlines()
    mutations = {
        "truncated_child": b"\n".join([header]+tokens[:-1])+b"\n",
        "surplus_child": raw+b"-1\n",
        "false_conflict_at_root": header+b"\n-1\n",
        "branch_on_already_fixed_tag": b"\n".join([header, b"0"]+tokens[1:])+b"\n",
    }
    rejected = []
    with tempfile.TemporaryDirectory(prefix="regression_", dir=audit.OUT) as td:
        td = Path(td)
        input_path, proof_path, zipped = td/"input.txt", td/"proof.txt", td/"proof.gz"
        text = f"9 5 {len(rows)}\n"+"".join(" ".join(map(str, row))+"\n" for row in rows)
        input_path.write_text(text)
        for name, corrupted in mutations.items():
            proof_path.write_bytes(corrupted)
            zipped.write_bytes(gzip.compress(corrupted, mtime=0))
            altered = dict(record, proof=str(zipped.relative_to(audit.OUT)),
                           proof_sha256_uncompressed=audit.sha(corrupted),
                           proof_bytes_uncompressed=len(corrupted))
            try:
                verify.check_tree(9, 5, rows, altered)
            except (AssertionError, StopIteration, ValueError):
                pass
            else:
                raise AssertionError(("Python accepted corrupted tree", name))
            native = subprocess.run([str(verify.FAST_CHECKER), str(input_path), str(proof_path)], capture_output=True, text=True)
            assert native.returncode != 0 and "INVALID CERTIFICATE" in native.stderr
            rejected.append(name)
    tests["both_checkers_reject_rehashed_malformed_trees"] = rejected

    # A deliberate weak-only CSP: both triples must have three distinct indices.
    instance = audit.make_instance(audit.singer(11), (0, 1, 2))
    weak_ids = [j for j, witness in enumerate(instance["witnesses"])
                if len(set(witness["left"])) == len(set(witness["right"])) == 3]
    weak = audit.solve(instance, row_ids=weak_ids)
    assert weak["status"] == "SAT"
    tags, v, k = weak["tags"], instance["v"], instance["k"]
    A = [c+k*((s-c)*pow(k, -1, v) % v) for s, c in zip(instance["T"], tags)]
    weak_sums = [(sum(A[j] for j in indices) % (v*k)) for indices in itertools.combinations(range(9), 3)]
    assert len(set(weak_sums)) == len(weak_sums) == 84
    seen = {}
    collision = None
    for indices in itertools.combinations_with_replacement(range(9), 3):
        residue = sum(A[j] for j in indices) % (v*k)
        if residue in seen:
            collision = {"left_indices": seen[residue], "right_indices": indices, "sum_mod_665": residue}
            assert len(set(indices)) < 3 or len(set(seen[residue])) < 3
            break
        seen[residue] = indices
    assert collision is not None
    try:
        audit.verify_sat(instance, tags)
    except AssertionError:
        pass
    else:
        raise AssertionError("strong checker accepted the weak-only fixture")
    tests["repeated_triples_negative_fixture"] = {
        "classification": "weak-only SAT, NOT strong B3; a negative regression test, not a construction success",
        "deleted_indices": [0, 1, 2], "T": instance["T"], "tags": tags, "CRT_A_in_T_order": A,
        "weak_distinct_triple_sums": 84, "weak_constraint_count": len(weak_ids),
        "strong_constraint_count": len(instance["rows"]), "strong_collision": collision,
    }
    tests["status"] = "PASS"
    assert audit.sha((audit.HERE/"Spec.lean").read_bytes()) == audit.SPEC_SHA256
    audit.write_json(audit.OUT/"regression_tests.json", tests)
    print(json.dumps(tests, indent=2))


if __name__ == "__main__":
    main()
