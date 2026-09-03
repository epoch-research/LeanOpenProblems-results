# Exact finite-field audit of the exceptional pencils in FreshB3Mechanisms.md.
# Run: sage Submission/fresh_b3_pencils_audit.sage
from itertools import combinations_with_replacement, combinations
from pathlib import Path
from collections import defaultdict
import json
import random
import numpy as np


def collision_masks(values, modulus=None):
    by_sum = defaultdict(list)
    masks = set()
    for tri in combinations_with_replacement(range(len(values)), 3):
        value = sum(values[i] for i in tri)
        if modulus is not None:
            value %= modulus
        mask = int(sum(1 << i for i in set(tri)))
        for prev in by_sum[value]:
            masks.add(mask | prev)
        by_sum[value].append(mask)
    return masks


def upward_closure(masks, number_of_bits):
    bad = np.zeros(int(1 << number_of_bits), dtype=np.bool_)
    if masks:
        bad[[int(mask) for mask in masks]] = True
    for i in range(number_of_bits):
        half = 1 << i
        blocks = bad.reshape((-1, 2 * half))
        blocks[:, half:] |= blocks[:, :half]
    return bad


def pencil_audit(alpha, beta, params, exhaustive=True):
    q = len(params)
    L = {u + v * alpha for u in params for v in params}
    P = {alpha**2 + u * alpha + v for u in params for v in params}
    E = {u for u in L if beta * u in P}
    assert len(E) == q and 0 not in E
    all_reps = defaultdict(list)
    exceptional_reps = defaultdict(list)
    checks = 0
    seed = random.Random(int(314159 + q))
    for t_idx, t in enumerate(params):
        edges = []
        for i, j in combinations_with_replacement(range(q), 2):
            value = (alpha - params[i]) * (alpha - params[j]) / (beta - t)
            all_reps[value].append((i, j, t_idx))
            if value in E:
                edges.append((i, j))
                exceptional_reps[value].append((i, j, t_idx))
        # A projective involution leaves at most one finite point paired to infinity.
        degrees = [0] * q
        for i, j in edges:
            degrees[i] += 1
            if i != j:
                degrees[j] += 1
        assert max(degrees) <= 1
        assert sum(d == 0 for d in degrees) <= 1
        if exhaustive:
            subsets = range(1 << q)
        else:
            subsets = [seed.randrange(1 << q) for _ in range(1000)]
            subsets += [(1 << i) - 1 for i in range(q + 1)]
        for mask in subsets:
            m = int(mask).bit_count()
            count = sum(bool(mask & (1 << i)) and bool(mask & (1 << j)) for i, j in edges)
            assert 2 * count >= 2 * m - (q + 1)
            checks += 1
    assert all(len(reps) == 1 for value, reps in all_reps.items() if value not in E)
    return exceptional_reps, {
        "exceptional_line_size": int(q),
        "exceptional_triples": int(sum(len(rs) for rs in exceptional_reps.values())),
        "maximum_exceptional_multiplicity": int(max(map(len, exceptional_reps.values()))),
        "nonexceptional_values": int(sum(value not in E for value in all_reps)),
        "subset_involution_checks": int(checks),
    }


def exceptional_collision_masks(first, second, q):
    masks = set()
    for reps_by_value, swapped in ((first, False), (second, True)):
        for reps in reps_by_value.values():
            rep_masks = []
            for i, j, t in reps:
                if not swapped:
                    mask = (1 << i) | (1 << j) | (1 << (q + t))
                else:
                    mask = (1 << (q + i)) | (1 << (q + j)) | (1 << t)
                rep_masks.append(mask)
            for a, b in combinations(rep_masks, 2):
                masks.add(a | b)
    return masks


def field_audit(q):
    F = GF(q, name='z')
    K = GF(q**3, name='a')
    alpha = K.gen()
    beta = alpha**2
    if F.is_prime_field():
        embedding = F.hom([K(z) for z in F.gens()], K)
    else:
        embedding = Hom(F, K).list()[0]
    params = [embedding(t) for t in F]
    assert beta not in {u + v * alpha for u in params for v in params}
    first, forward = pencil_audit(alpha, beta, params, q <= 13)
    second, reverse = pencil_audit(beta, alpha, params, q <= 13)
    record = {"q": int(q), "forward": forward, "reverse": reverse}
    # This check is logically independent of the pencil computation:
    # logarithms and all repeated triple sums are enumerated directly.
    if q <= 11:
        g = K.multiplicative_generator()
        M = int(q**3 - 1)
        bs = [int(discrete_log(alpha-t, g)) for t in params]
        cs = [int(discrete_log((beta-t)**(-1), g)) for t in params]
        assert not collision_masks(bs, M)
        assert not collision_masks(cs, M)
        values = [int(4*b+1) for b in bs] + [int(4*c+2) for c in cs]
        assert len(set(values)) == 2*q
        cyclic_masks = collision_masks(values, 4*M)
        from_pencils = exceptional_collision_masks(first, second, q)
        assert cyclic_masks == from_pencils
        integer_masks = collision_masks(values)
        assert integer_masks <= cyclic_masks
        record["cyclic_collision_masks"] = len(cyclic_masks)
        record["integer_collision_masks"] = len(integer_masks)
        # Exhaust all parameter subsets for q<=9; no extrapolation from this is used.
        if q <= 9:
            details = {}
            for name, masks, factor in (("cyclic", cyclic_masks, 1), ("integer", integer_masks, 3)):
                bad = upward_closure(masks, 2*q)
                valid = np.flatnonzero(~bad)
                maximum, witness = -1, None
                for raw in valid:
                    mask = int(raw)
                    m = int(mask & ((1 << q)-1)).bit_count()
                    n = int(mask >> q).bit_count()
                    assert n*(2*m-(q+1)) <= 2*factor*q
                    assert m*(2*n-(q+1)) <= 2*factor*q
                    assert (m+n)*(m+n-(q+1)) <= 4*factor*q
                    if m+n > maximum:
                        maximum, witness = m+n, mask
                selected = [values[i] for i in range(2*q) if witness & (1 << i)]
                # Recheck the returned maximizer by direct triple enumeration.
                assert not collision_masks(selected, 4*M if name == "cyclic" else None)
                details[name] = {
                    "admissible_parameter_subsets": int(len(valid)),
                    "maximum_cardinality": int(maximum),
                    "example_integer_set": selected,
                    "fixed_ambient_N": int(4*M),
                }
            record["all_subsets_audit"] = details
    return record


records = []
for q in [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19]:
    record = field_audit(q)
    records.append(record)
    print(json.dumps(record), flush=True)
general_basis_checks = []
for q in [3, 5, 7]:
    K = GF(q**3, name='w')
    alpha = K.gen()
    params = [K(t) for t in GF(q)]
    L = {u + v*alpha for u in params for v in params}
    betas = [beta for beta in K if beta not in L]
    checks = 0
    for beta in betas:
        _, fwd = pencil_audit(alpha, beta, params, True)
        _, rev = pencil_audit(beta, alpha, params, True)
        checks += fwd['subset_involution_checks'] + rev['subset_involution_checks']
    summary = {'q': int(q), 'all_basis_choices_beta': len(betas), 'subset_involution_checks': int(checks)}
    general_basis_checks.append(summary)
    print(json.dumps(summary), flush=True)
result = {
    "status": "Finite verification of the proved exceptional-pencil mechanism; not a resolution of the conjecture",
    "definition": "strong B3 with repeated summands",
    "records": records,
    "general_basis_checks": general_basis_checks,
}
# Sage's preparser runs a generated .sage.py file; keep the intended stable output name.
out = Path('Submission/fresh_b3_pencils_audit.json')
out.write_text(json.dumps(result, indent=2) + '\n')
