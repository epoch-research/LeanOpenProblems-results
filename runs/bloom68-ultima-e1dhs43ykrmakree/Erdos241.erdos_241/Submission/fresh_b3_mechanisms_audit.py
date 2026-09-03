#!/usr/bin/env python3
"""Exact audit of the explicit family in FreshB3Mechanisms.md.

All triples are multisets, including repeated indices. This script is an
independent finite check, not the proof of the unbounded-family statement.
"""
from itertools import combinations_with_replacement
from collections import Counter
from decimal import Decimal, localcontext
from pathlib import Path
import json


def is_b3(values, modulus=None):
    sums = {}
    for triple in combinations_with_replacement(range(len(values)), 3):
        value = sum(values[i] for i in triple)
        if modulus is not None:
            value %= modulus
        if value in sums:
            return False, (sums[value], triple, value)
        sums[value] = triple
    return True, len(sums)


def audit(r):
    assert r >= 5 and r % 2 == 1
    base = 7
    scale = 3 * r
    bound = scale * base ** r
    ys = [scale * base ** i for i in range(r)]
    xs = [bound + i - ys[i - 1] - ys[i] for i in range(r)]
    values = xs + ys
    assert len(set(values)) == 2 * r
    assert min(values) >= 1 and max(values) <= bound
    ok, triple_count = is_b3(values)
    assert ok, triple_count
    assert triple_count == (2 * r) * (2 * r + 1) * (2 * r + 2) // 6
    diffs = {a - b for a in values for b in values if a != b}
    assert len(diffs) == 2 * r * (2 * r - 1)
    assert 1 not in diffs
    witnesses = set()
    for i in range(1, r):
        pos = (xs[i], ys[i])
        neg = (xs[i - 1], ys[(i - 2) % r])
        assert len(set(pos + neg)) == 4
        assert sum(pos) - sum(neg) == 1
        for j, k in ((0, 1), (1, 0)):
            d1, d2 = pos[0] - neg[j], pos[1] - neg[k]
            assert d1 + d2 == 1
            for pair in ((d1, d2), (d2, d1)):
                assert pair not in witnesses
                witnesses.add(pair)
    assert len(witnesses) == 4 * (r - 1)
    mu1 = sum(1 - d in diffs for d in diffs)
    assert mu1 >= 4 * (r - 1)
    with localcontext() as ctx:
        ctx.prec = 18
        ratio = str(Decimal((2 * r) ** 3) / Decimal(bound))
    return {
        "r": r, "base": base, "scale": scale, "cardinality": len(values),
        "ambient_N_decimal_digits": len(str(bound)),
        "repeated_triples_checked": triple_count,
        "nonzero_differences": len(diffs),
        "one_is_a_difference": False,
        "mu_one": mu1,
        "proved_lower_bound": 4 * (r - 1),
        "cardinality_cubed_over_N": ratio,
    }


def exhaustive_pointwise_audit(last=12):
    count = checked_x = 0
    for mask in range(1 << (last + 1)):
        values = [i for i in range(last + 1) if mask & (1 << i)]
        ok, _ = is_b3(values)
        if not ok:
            continue
        count += 1
        diffs = {a-b for a in values for b in values if a != b}
        mu = Counter(d+e for d in diffs for e in diffs)
        for x, multiplicity in mu.items():
            if x != 0 and x not in diffs:
                assert multiplicity <= 2*len(values)
                checked_x += 1
    return {"ambient_window": [0, last], "all_strong_B3_subsets": count,
            "nontrivial_pointwise_bounds_checked": checked_x}


if __name__ == "__main__":
    records = [audit(r) for r in (5, 7, 9, 11, 15, 21, 31, 51)]
    result = {
        "status": "Verified partial results only; conjecture unresolved",
        "definition": "strong B3; all multiset triples, repetitions allowed",
        "family_audits": records,
        "exhaustive_pointwise_audit": exhaustive_pointwise_audit(),
    }
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
