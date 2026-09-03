#!/usr/bin/env python3
"""Targeted exact Singer half-tag coherence audit (prime q=11,17).

No arbitrary-set search, no second-tag normalization, no PGL2 identification.
The C++ search fixes only c[0]=0. All triples are multisets, including repeats.
Run --help for the reproducible phases. The independent checker is
singer_half_tag_verify.py.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import gzip
import hashlib
import itertools as it
import json
import math
from pathlib import Path
import subprocess
import tempfile
import time

import random
HERE = Path(__file__).resolve().parent
OUT = HERE / "singer_half_tag_results"
CPP = HERE / "singer_half_tag_coherence.cpp"
BINARY = Path(tempfile.gettempdir()) / "singer_half_tag_solver"
SPEC_SHA256 = "fa08ffd0daf6d26c138eb7da5a4186d0abd9155428d0c4528526a570b398d860"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2) + "\n")
    tmp.replace(path)


def prime_factors(n):
    ans = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            ans.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        ans.append(n)
    return ans


class CubicField:
    """F_q[x]/(x^3+f[2]x^2+f[1]x+f[0]), encoded a0+q*a1+q^2*a2."""
    def __init__(self, q, polynomial=None):
        assert q >= 5 and q % 2 == 1 and q % 3 == 2
        assert all(q % d for d in range(2, math.isqrt(q) + 1)), "prime q only"
        self.q = q
        if polynomial is None:
            polynomial = next(
                (a, b, c) for a in range(1, q) for b in range(q) for c in range(q)
                if all((x**3 + c*x*x + b*x + a) % q for x in range(q))
            )
        self.f = tuple(polynomial)
        assert all((x**3 + self.f[2]*x*x + self.f[1]*x + self.f[0]) % q for x in range(q))

    def decode(self, a):
        q = self.q
        return a % q, (a // q) % q, a // (q*q)

    def encode(self, a):
        q = self.q
        return sum((x % q) * q**i for i, x in enumerate(a))

    def add(self, *args):
        return self.encode(map(sum, zip(*(self.decode(a) for a in args))))

    def mul(self, a, b):
        aa, bb = self.decode(a), self.decode(b)
        cc = [0] * 5
        for i in range(3):
            for j in range(3):
                cc[i+j] += aa[i]*bb[j]
        for d in (4, 3):
            for i in range(3):
                cc[d-3+i] -= cc[d]*self.f[i]
        return self.encode(cc[:3])

    def power(self, a, e):
        out = 1
        while e:
            if e & 1:
                out = self.mul(out, a)
            a = self.mul(a, a)
            e >>= 1
        return out

    def trace(self, a):
        return self.add(a, self.power(a, self.q), self.power(a, self.q*self.q))


@lru_cache(None)
def singer(q):
    field = CubicField(q)
    order = q**3 - 1
    factors = prime_factors(order)
    generator = next(g for g in range(2, q**3)
                     if all(field.power(g, order//p) != 1 for p in factors))
    assert field.power(generator, order) == 1
    v, k = q*q+q+1, (q-1)//2
    assert math.gcd(v, k) == 1
    S, z = [], 1
    for exponent in range(v):
        if field.trace(z) == 0:
            S.append(exponent)
        z = field.mul(z, generator)
    assert len(S) == q + 1
    counts = Counter((a-b) % v for a in S for b in S if a != b)
    assert counts == Counter({r: 1 for r in range(1, v)})
    return {
        "q": q, "k": k, "v": v, "M": v*k,
        "polynomial_low_coefficients": list(field.f),
        "generator_encoded": generator, "generator_coefficients": list(field.decode(generator)),
        "multiplicative_order": order, "order_prime_factors": factors,
        "S": S, "perfect_difference_counts": [counts[r] for r in range(v)],
        "gcd_v_k": math.gcd(v, k), "construction": "trace-zero logs of a primitive F_(q^3) element modulo v",
    }


def orient(row):
    row = tuple(row)
    first = next(x for x in row if x)
    return row if first > 0 else tuple(-x for x in row)


def make_instance(construction, deleted):
    S, v, k = construction["S"], construction["v"], construction["k"]
    deleted = tuple(sorted(deleted))
    assert len(set(deleted)) == len(deleted) and all(0 <= i < len(S) for i in deleted)
    retained = [i for i in range(len(S)) if i not in deleted]
    T = [S[i] for i in retained]
    n = len(T)
    fibers = defaultdict(list)
    for triple in it.combinations_with_replacement(range(n), 3):
        fibers[sum(T[i] for i in triple) % v].append(triple)
    witnesses = {}
    raw_pairs = 0
    for h, triples in fibers.items():
        for left, right in it.combinations(triples, 2):
            raw_pairs += 1
            row = [0]*n
            for i in left:
                row[i] += 1
            for i in right:
                row[i] -= 1
            canonical = orient(row)
            if canonical != tuple(row):
                left, right = right, left
            assert sum(canonical) == 0 and max(map(abs, canonical)) <= 3
            witnesses[canonical] = {"left": list(left), "right": list(right), "base_sum": h}
    rows = sorted(witnesses)
    signed = defaultdict(set)
    for i, t in enumerate(T):
        row = [0]*n
        row[i] = 1
        signed[t].add(tuple(row))
    for a, b in it.combinations_with_replacement(range(n), 2):
        for c in range(n):
            if c == a or c == b:
                continue
            row = [0]*n
            row[a] += 1
            row[b] += 1
            row[c] -= 1
            signed[(T[a]+T[b]-T[c]) % v].add(tuple(row))
    saturated = []
    for h in sorted(signed):
        vectors = sorted(signed[h])
        if len(vectors) == k:
            saturated.append({"h": h, "vectors": vectors,
                              "sum_row": [sum(x[i] for x in vectors) for i in range(n)],
                              "rhs": k*(k-1)//2 % k})
    assert sum(len(xs) for xs in fibers.values()) == math.comb(n+2, 3)
    assert sum(map(len, signed.values())) == n*n*(n-1)//2+n
    return {
        "q": construction["q"], "v": v, "k": k, "n": n,
        "deleted_indices": list(deleted), "deleted_points": [S[i] for i in deleted],
        "retained_indices": retained, "T": T, "rows": rows,
        "witnesses": [witnesses[r] for r in rows],
        "triple_multisets": math.comb(n+2, 3), "raw_collision_pairs": raw_pairs,
        "triple_fiber_histogram": dict(sorted(Counter(len(fibers[h]) for h in range(v)).items())),
        "signed_fiber_histogram": dict(sorted(Counter(len(signed[h]) for h in range(v)).items())),
        "signed_fiber_max": max(map(len, signed.values())), "saturated": saturated,
    }


def input_bytes(instance, row_ids=None):
    rows = instance["rows"] if row_ids is None else [instance["rows"][j] for j in row_ids]
    return (f'{instance["n"]} {instance["k"]} {len(rows)}\n' +
            "".join(" ".join(map(str, row)) + "\n" for row in rows)).encode()


def compile_solver():
    subprocess.run(["g++", "-O3", "-std=c++17", "-Wall", "-Wextra", "-pedantic", str(CPP), "-o", str(BINARY)], check=True)
    test = json.loads(subprocess.check_output([str(BINARY), "--self-test"]))
    assert test["status"] == "PASS"
    return test


def solve(instance, proof_name=None, timeout_ms=0, node_cap=0, row_ids=None):
    data = input_bytes(instance, row_ids)
    with tempfile.TemporaryDirectory(prefix="singer_half_tag_") as td:
        infile, proof = Path(td)/"instance.txt", Path(td)/"proof.txt"
        infile.write_bytes(data)
        cmd = [str(BINARY), str(infile), str(max(0, timeout_ms)), str(proof) if proof_name else "-", str(node_cap)]
        # The internal deadline is exact; this external guard never turns an interrupted run into UNSAT.
        try:
            output = subprocess.check_output(cmd, timeout=timeout_ms/1000+1 if timeout_ms else None)
            answer = json.loads(output)
        except subprocess.TimeoutExpired:
            answer = {"status": "TIMEOUT", "reason": "external wall-clock guard", "tags": []}
        if answer["status"] == "UNSAT" and proof_name:
            raw = proof.read_bytes()
            path = OUT / "proofs" / (proof_name + ".proof.gz")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(gzip.compress(raw, mtime=0))
            answer["proof"] = str(path.relative_to(OUT))
            answer["proof_sha256_uncompressed"] = sha(raw)
            answer["proof_bytes_uncompressed"] = len(raw)
        answer["input_sha256"] = sha(data)
        return answer


def verify_sat(instance, tags):
    """Direct check in the genuinely cyclic CRT group, not just the generated rows."""
    n, v, k = instance["n"], instance["v"], instance["k"]
    assert len(tags) == n and all(0 <= x < k for x in tags)
    assert math.gcd(v, k) == 1
    M = v*k
    inv = pow(v, -1, k)
    A = [(s + v*((c-s)*inv % k)) % M for s, c in zip(instance["T"], tags)]
    assert len(set(A)) == n
    assert all(a % v == s and a % k == c for a, s, c in zip(A, instance["T"], tags))
    triples = {}
    for indices in it.combinations_with_replacement(range(n), 3):
        residue = sum(A[i] for i in indices) % M
        if residue in triples:
            raise AssertionError(("B3 collision", triples[residue], indices, residue))
        triples[residue] = indices
    pair_sums = [sum(A[i] for i in pair) % M for pair in it.combinations_with_replacement(range(n), 2)]
    assert len(set(pair_sums)) == len(pair_sums)
    return {"CRT_A_in_T_order": A, "M": M, "distinct_triple_sums": len(triples),
            "triple_multisets": math.comb(n+2, 3), "distinct_pair_sums": len(pair_sums), "strong_B3": True}


def instance_record(instance):
    return {key: instance[key] for key in (
        "deleted_indices", "deleted_points", "retained_indices", "T", "n", "triple_multisets",
        "raw_collision_pairs", "triple_fiber_histogram", "signed_fiber_histogram", "signed_fiber_max")}


def linear_saturated_certificate(instance):
    """Odd prime tags: homogeneous saturated-fiber identities may force an inequality to be zero."""
    p, n = instance["k"], instance["n"]
    if p <= 2 or prime_factors(p) != [p]:
        return None  # Even k has a nonzero RHS; no invalid homogeneous-field test.
    fibers = instance["saturated"]
    assert all(f["rhs"] == 0 for f in fibers)
    basis = {}
    for j, f in enumerate(fibers):
        row = [x % p for x in f["sum_row"]]
        combination = [int(t == j) for t in range(len(fibers))]
        for col in sorted(basis):
            if row[col]:
                mult = row[col]
                r, co = basis[col]
                row = [(x-mult*y) % p for x, y in zip(row, r)]
                combination = [(x-mult*y) % p for x, y in zip(combination, co)]
        pivot = next((i for i, x in enumerate(row) if x), None)
        if pivot is not None:
            scale = pow(row[pivot], -1, p)
            basis[pivot] = ([x*scale % p for x in row], [x*scale % p for x in combination])
    for row_id, target in enumerate(instance["rows"]):
        rem = [x % p for x in target]
        combination = [0]*len(fibers)
        for col in sorted(basis):
            if rem[col]:
                mult = rem[col]
                row, co = basis[col]
                rem = [(x-mult*y) % p for x, y in zip(rem, row)]
                combination = [(x+mult*y) % p for x, y in zip(combination, co)]
        if not any(rem):
            used = [j for j, x in enumerate(combination) if x]
            core = {row_id}
            row_index = {r: i for i, r in enumerate(instance["rows"])}
            for j in used:
                for a, b in it.combinations(fibers[j]["vectors"], 2):
                    core.add(row_index[orient(x-y for x, y in zip(a, b))])
            return {"rank": len(basis), "saturated_count": len(fibers),
                    "target_constraint": row_id,
                    "fiber_multipliers": [{"fiber": j, "h": fibers[j]["h"], "multiplier": combination[j]} for j in used],
                    "core_constraint_ids": sorted(core)}
    return {"rank": len(basis), "saturated_count": len(fibers), "target_constraint": None}


def q11_all():
    construction = singer(11)
    results = {"construction": construction, "scope": "all 220 three-point deletions; no deletion symmetry reduction",
               "fixed_tag": "first retained point has tag zero; all other tags range over Z/5", "instances": []}
    start = time.monotonic()
    for deleted in it.combinations(range(12), 3):
        instance = make_instance(construction, deleted)
        assert instance["signed_fiber_max"] <= instance["k"]
        answer = solve(instance, "q11_d_" + "_".join(map(str, deleted)))
        record = instance_record(instance)
        record.update(answer)
        record["saturated_linear_test"] = linear_saturated_certificate(instance)
        if answer["status"] == "SAT":
            record["verification"] = verify_sat(instance, answer["tags"])
        results["instances"].append(record)
        if len(results["instances"]) % 20 == 0:
            print("q11", len(results["instances"]), dict(Counter(x["status"] for x in results["instances"])), flush=True)
    results["summary"] = {
        "deletions_tested": len(results["instances"]), "status_counts": dict(Counter(x["status"] for x in results["instances"])),
        "nodes": sum(x["nodes"] for x in results["instances"]),
        "covered_normalized_assignments": sum(x["covered_assignments"] for x in results["instances"]),
        "normalized_assignments_per_instance": 5**8,
        "max_signed_fiber": max(x["signed_fiber_max"] for x in results["instances"]),
        "saturated_linear_obstructions": sum(x["saturated_linear_test"]["target_constraint"] is not None for x in results["instances"]),
        "search_elapsed_ms": sum(x["elapsed_ms"] for x in results["instances"]),
        "phase_wall_seconds": time.monotonic()-start,
    }
    assert results["summary"]["deletions_tested"] == math.comb(12, 3)
    write_json(OUT / "q11_three_deletions.json", results)
    print(json.dumps(results["summary"], indent=2), flush=True)


def q11_retention():
    """Find the exact maximum retained size; all larger sizes are covered by heredity."""
    previous = json.loads((OUT/"q11_three_deletions.json").read_text())
    assert len(previous["instances"]) == 220 and all(x["status"] == "UNSAT" for x in previous["instances"])
    construction = singer(11)
    results = {"construction": construction,
               "upper_bound_source": "q11_three_deletions.json (all nine-point subsets UNSAT)",
               "scope": "test successive retained sizes, lexicographic deletions, stop at first verified SAT",
               "instances": []}
    start = time.monotonic()
    for number_deleted in range(4, 12):
        n = 12-number_deleted
        for deleted in it.combinations(range(12), number_deleted):
            instance = make_instance(construction, deleted)
            answer = solve(instance, "q11_retention_d_" + "_".join(map(str, deleted)))
            record = instance_record(instance)
            record.update(answer)
            if answer["status"] == "SAT":
                record["verification"] = verify_sat(instance, answer["tags"])
            results["instances"].append(record)
            if answer["status"] == "SAT":
                results["summary"] = {"exact_maximum_retention": n,
                                      "witness_deleted_indices": list(deleted),
                                      "status_counts": dict(Counter(x["status"] for x in results["instances"])),
                                      "tested_by_retained_size": dict(Counter(x["n"] for x in results["instances"])),
                                      "phase_wall_seconds": time.monotonic()-start}
                write_json(OUT/"q11_retention.json", results)
                print(json.dumps(results["summary"], indent=2))
                print("SAT witness", json.dumps(record, indent=2))
                return
        print("q11 retention: all", math.comb(12, number_deleted), "subsets of size", n, "UNSAT", flush=True)
    raise AssertionError("a singleton must be SAT")


def rank_mod(rows, p):
    basis = {}
    for original in rows:
        row = [x % p for x in original]
        for col in sorted(basis):
            if row[col]:
                scale = row[col]
                row = [(x-scale*y) % p for x, y in zip(row, basis[col])]
        col = next((i for i, x in enumerate(row) if x), None)
        if col is not None:
            scale = pow(row[col], -1, p)
            basis[col] = [x*scale % p for x in row]
    return len(basis)


def d4_certificate(instance, core):
    """Recognize an exact integer D4 arrangement: 2*L_i +/- 2*L_j = +/-2*row.

    This is structural recognition of a core, not an additional search assumption.
    Division by 2 is legitimate here because the tag group is Z/5.
    """
    if len(core) != 12 or instance["k"] != 5:
        return None
    rows = [instance["rows"][j] for j in core]
    add = lambda u, v: tuple(x+y for x, y in zip(u, v))
    sub = lambda u, v: tuple(x-y for x, y in zip(u, v))
    scale = lambda a, u: tuple(a*x for x in u)
    lookup = {scale(2*sign, row): (row_id, sign)
              for row_id, row in zip(core, rows) for sign in (1, -1)}
    u = rows[0]
    for v in rows[1:]:
        first = [add(u, v), sub(u, v)]
        candidates = sorted({sub(w, first[0]) for w in lookup
                             if all(add(x, sub(w, first[0])) in lookup and sub(x, sub(w, first[0])) in lookup
                                    for x in first)})
        for z, w in it.combinations(candidates, 2):
            if add(z, w) not in lookup or sub(z, w) not in lookup:
                continue
            forms = first+[z, w]
            mapping = []
            for i, j in it.combinations(range(4), 2):
                for sign in (1, -1):
                    vector = add(forms[i], scale(sign, forms[j]))
                    row_id, row_sign = lookup[vector]
                    mapping.append({"i": i, "j": j, "sign": sign,
                                    "constraint_id": row_id, "row_sign": row_sign})
            if {x["constraint_id"] for x in mapping} == set(core):
                return {"twice_linear_forms": forms, "pair_mapping": mapping,
                        "negation_orbits_mod_5": [[0], [1, 4], [2, 3]],
                        "contradiction": "four values must occupy distinct negation orbits, but Z/5 has only three"}
    return None


def q11_cores():
    previous = json.loads((OUT/"q11_three_deletions.json").read_text())
    construction = singer(11)
    fewest = min(previous["instances"], key=lambda r: (r["raw_collision_pairs"], r["deleted_indices"]))
    cases = [(0, 1, 2), (0, 1, 7), (0, 2, 6), tuple(fewest["deleted_indices"])]
    result = {"construction": construction,
              "method": "greedy constraint deletion in 8 deterministic orders, plus the saturated-linear core if present; inclusion-minimal, not minimum-cardinality",
              "cases": []}
    for deleted in dict.fromkeys(cases):
        instance = make_instance(construction, deleted)
        linear = linear_saturated_certificate(instance)
        starts = [list(range(len(instance["rows"]))) for _ in range(8)]
        starts[1].reverse()
        for seed in range(2, 8):
            random.Random(241000+seed).shuffle(starts[seed])
        if linear["target_constraint"] is not None:
            starts.append(linear["core_constraint_ids"][:])
            starts.append(list(reversed(linear["core_constraint_ids"])))
        candidates = []
        calls = 0
        for order in starts:
            active = sorted(order)
            for row_id in order:
                trial = [j for j in active if j != row_id]
                answer = solve(instance, row_ids=trial)
                calls += 1
                if answer["status"] == "UNSAT":
                    active = trial
                else:
                    assert answer["status"] == "SAT"
            candidates.append(active)
        core = min(candidates, key=lambda xs: (len(xs), xs))
        answer = solve(instance, "q11_core_d_" + "_".join(map(str, deleted)), row_ids=core)
        assert answer["status"] == "UNSAT"
        critical = []
        for row_id in core:
            trial = [j for j in core if j != row_id]
            sat = solve(instance, row_ids=trial)
            assert sat["status"] == "SAT"
            tags = sat["tags"]
            assert all(sum(x*y for x, y in zip(instance["rows"][j], tags)) % 5 != 0 for j in trial)
            assert sum(x*y for x, y in zip(instance["rows"][row_id], tags)) % 5 == 0
            critical.append({"removed_constraint": row_id, "tags_satisfying_other_core_constraints": tags})
        record = instance_record(instance)
        record["input_sha256"] = sha(input_bytes(instance))
        record["saturated_linear_test"] = linear
        record["saturated_fibers"] = instance["saturated"]
        record["core"] = dict(answer, constraint_ids=core, rows=[instance["rows"][j] for j in core],
                              witnesses=[instance["witnesses"][j] for j in core],
                              rank_mod_5=rank_mod([instance["rows"][j] for j in core], 5),
                              criticality_witnesses=critical,
                              candidate_core_sizes=[len(xs) for xs in candidates], solver_calls=calls+1+len(core))
        record["core"]["D4_certificate"] = d4_certificate(instance, core)
        result["cases"].append(record)
        print("q11 core", deleted, "size", len(core), "rank", record["core"]["rank_mod_5"], "candidates", record["core"]["candidate_core_sizes"], "D4", bool(record["core"]["D4_certificate"]), flush=True)
    write_json(OUT/"q11_cores.json", result)


def frobenius_orbits(construction):
    """Only a genuine group automorphism: (s,c) -> (q*s,c), or x -> q*x in CRT."""
    S, q, v, k = (construction[key] for key in ("S", "q", "v", "k"))
    index = {s: i for i, s in enumerate(S)}
    permutation = [index[q*s % v] for s in S]
    assert sorted(permutation) == list(range(len(S)))
    assert all(permutation[permutation[permutation[i]]] == i for i in range(len(S)))
    assert q % k == 1 and math.gcd(q, v*k) == 1
    unused = set(it.combinations(range(len(S)), 3))
    orbits = []
    while unused:
        start = min(unused)
        orbit, d = set(), start
        while d not in orbit:
            orbit.add(d)
            d = tuple(sorted(permutation[i] for i in d))
        assert d == start and len(orbit) in (1, 3)
        unused.difference_update(orbit)
        orbits.append({"representative": list(min(orbit)), "members": [list(x) for x in sorted(orbit)]})
    return permutation, orbits


def q17_capped():
    """One total 300-second wall-clock search phase, with <=5 seconds per representative.

    Construction, target selection, input/output, and proof compression are inside
    this budget. Certificate verification is a separate, non-search phase.
    No earlier q=17 tag searches are needed. TIMEOUT is never promoted to UNSAT.
    """
    start = time.monotonic()
    budget_seconds = 300.0
    deadline = start+budget_seconds
    construction = singer(17)
    permutation, orbits = frobenius_orbits(construction)
    by_rep = {tuple(o["representative"]): o for o in orbits}
    owner = {tuple(d): rep for rep, o in by_rep.items() for d in o["members"]}
    profiles = []
    for rep in sorted(by_rep):
        instance = make_instance(construction, rep)
        assert instance["signed_fiber_max"] <= 8
        profiles.append({"representative": list(rep), "constraints": len(instance["rows"]),
                         "saturated_fibers": len(instance["saturated"]),
                         "signed_fiber_max": instance["signed_fiber_max"]})
    priority = []
    def target(d):
        rep = owner[tuple(sorted(d))]
        if rep not in priority:
            priority.append(rep)
    for d in ((0, 1, 2), (0, 6, 12), (15, 16, 17)):
        target(d)
    for o in orbits:
        if len(o["members"]) == 1:
            target(o["representative"])
    for key in ("constraints", "saturated_fibers"):
        target(min(profiles, key=lambda r: (r[key], r["representative"]))["representative"])
        target(max(profiles, key=lambda r: (r[key], r["representative"]))["representative"])
    ranked = sorted(profiles, key=lambda r: (r["constraints"], r["saturated_fibers"], r["representative"]))
    for j in range(16):
        target(ranked[(len(ranked)-1)*j//15]["representative"])
    order = priority+[rep for rep in sorted(by_rep) if rep not in priority]
    results = {"construction": construction,
               "scope": "targeted extremes, six Frobenius-fixed deletions, and constraint-profile quantiles first; then other exact Frobenius representatives while budget remains",
               "fixed_tag": "first retained point is zero; every other tag arbitrary in Z/8",
               "symmetry": {"map_H": "s -> 17*s mod 307", "map_K": "c -> c", "map_CRT": "x -> 17*x mod 2456",
                            "permutation_of_S_indices": permutation, "orbit_partition": orbits,
                            "justification": "trace zero is Frobenius-invariant; 17 is a unit modulo 2456 and is 1 modulo 8; no PGL2 reparametrization used"},
               "budget_seconds": budget_seconds, "per_representative_cap_ms": 5000,
               "profiles": profiles, "target_priority_representatives": [list(d) for d in priority],
               "requested_representative_order": [list(d) for d in order], "instances": []}
    for deleted in order:
        remaining = deadline-time.monotonic()
        # Two seconds of headroom for the watchdog and final output prevent budget overrun.
        if remaining <= 2:
            break
        instance = make_instance(construction, deleted)
        timeout_ms = min(5000, int((deadline-time.monotonic()-2)*1000))
        if timeout_ms <= 0:
            break
        answer = solve(instance, "q17_d_"+"_".join(map(str, deleted)), timeout_ms=timeout_ms)
        record = instance_record(instance)
        record.update(answer)
        record["timeout_ms"] = timeout_ms
        record["orbit_members"] = by_rep[deleted]["members"]
        if answer["status"] == "SAT":
            record["verification"] = verify_sat(instance, answer["tags"])
        results["instances"].append(record)
        if len(results["instances"]) <= 3 or len(results["instances"]) % 10 == 0:
            print("q17", len(results["instances"]), "of", len(order),
                  dict(Counter(x["status"] for x in results["instances"])),
                  "wall", round(time.monotonic()-start, 3), flush=True)
    attempted = {tuple(x["deleted_indices"]) for x in results["instances"]}
    results["unattempted_representatives"] = [list(d) for d in order if d not in attempted]
    original_counts = Counter()
    for record in results["instances"]:
        original_counts[record["status"]] += len(record["orbit_members"])
    original_counts["UNTESTED_BUDGET"] = sum(len(by_rep[d]["members"]) for d in order if d not in attempted)
    assert sum(original_counts.values()) == math.comb(18, 3)
    results["summary"] = {
        "total_deletions": math.comb(18, 3), "Frobenius_orbits": len(orbits),
        "orbit_size_histogram": dict(Counter(len(o["members"]) for o in orbits)),
        "representatives_attempted": len(results["instances"]),
        "representative_status_counts": dict(Counter(x["status"] for x in results["instances"])),
        "original_deletion_status_counts_via_valid_symmetry": dict(original_counts),
        "unattempted_representatives": len(results["unattempted_representatives"]),
        "nodes": sum(x.get("nodes", 0) for x in results["instances"]),
        "normalized_assignments_per_representative": 8**14,
        "covered_assignments_in_UNSAT_representatives": sum(x["covered_assignments"] for x in results["instances"] if x["status"] == "UNSAT"),
        "max_signed_fiber_all_deletions_via_symmetry": max(p["signed_fiber_max"] for p in profiles),
        "search_elapsed_ms": sum(x.get("elapsed_ms", 0) for x in results["instances"]),
        "phase_wall_seconds": time.monotonic()-start,
        "all_816_deletions_UNSAT": original_counts["UNSAT"] == math.comb(18, 3),
    }
    write_json(OUT/"q17_three_deletions.json", results)
    print(json.dumps(results["summary"], indent=2), flush=True)


def prepare():
    test = compile_solver()
    assert sha((HERE/"Spec.lean").read_bytes()) == SPEC_SHA256, "Spec.lean changed"
    data = {"solver_self_test": test, "spec_sha256": SPEC_SHA256,
            "constructions": [singer(q) for q in (11, 17)],
            "compiler": subprocess.check_output(["g++", "--version"], text=True).splitlines()[0]}
    write_json(OUT / "construction.json", data)
    for c in data["constructions"]:
        instance = make_instance(c, (0, 1, 2))
        print("q", c["q"], "polynomial", c["polynomial_low_coefficients"], "generator", c["generator_coefficients"], "S", c["S"])
        print("sample", {k: instance[k] for k in ("n", "raw_collision_pairs", "signed_fiber_histogram", "signed_fiber_max")})
        print("saturated-linear", linear_saturated_certificate(instance))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["prepare", "q11", "retention", "cores", "q17"])
    args = parser.parse_args()
    if args.phase == "prepare":
        prepare()
    else:
        compile_solver()
        {"q11": q11_all, "retention": q11_retention, "cores": q11_cores, "q17": q17_capped}[args.phase]()


if __name__ == "__main__":
    main()
