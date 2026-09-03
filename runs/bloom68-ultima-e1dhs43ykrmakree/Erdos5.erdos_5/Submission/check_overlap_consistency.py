#!/usr/bin/env python3
"""Exact finite analogue of the global parity coupling, NOT a prime-gap test.

Four labels, two in each pool. Each label has three divisor-observation
bits. One global coin selects a pool; its marks have even bit parity,
the other pool has odd parity. A prime flag means all three bits are 0.
All proper-subset bit moments agree between the two parity laws.
"""
from fractions import Fraction as Q
from itertools import product, combinations

BITS = tuple(product((0, 1), repeat=3))
SECTORS = {s: tuple(b for b in BITS if sum(b) % 2 == s) for s in (0, 1)}
MONOMIALS = tuple(S for r in range(3) for S in combinations(range(3), r))
POOL = (0, 0, 1, 1)


def prod(xs):
    ans = 1
    for x in xs:
        ans *= x
    return ans


def mono(b, S):
    return prod(b[j] for j in S)


rows = []
for active in (0, 1):
    for marks in product(*(SECTORS[0 if g == active else 1] for g in POOL)):
        flags = tuple(int(b == (0, 0, 0)) for b in marks)
        assert not (any(flags[:2]) and any(flags[2:]))
        rows.append((marks, flags))
assert len(rows) == 512

# The table is a single probability space for every overlapping test.
# Compute all proper-subset mass moments and one-prime moments exactly.
mass = {}
first = {}
for obs in product(MONOMIALS, repeat=4):
    values = [prod(mono(marks[h], obs[h]) for h in range(4)) for marks, _ in rows]
    actual = Q(sum(values), len(rows))
    target = Q(1, 2 ** sum(map(len, obs)))
    assert actual == target
    mass[obs] = actual
    for anchor in range(4):
        actual_p = Q(sum(v * flags[anchor] for v, (_, flags) in zip(values, rows)), len(rows))
        target_p = Q(0) if obs[anchor] else Q(1, 8) * Q(1, 2 ** sum(len(obs[h]) for h in range(4) if h != anchor))
        assert actual_p == target_p
        first[anchor, obs] = actual_p

# All prime-pattern factors, including overlapping tuples, share one law.
patterns = 0
for r in range(1, 5):
    for S in combinations(range(4), r):
        actual = Q(sum(prod(flags[h] for h in S) for _, flags in rows), len(rows))
        target = Q(2 ** (r - 1), 8 ** r) if len({POOL[h] for h in S}) == 1 else Q(0)
        assert actual == target
        patterns += 1

# Shared linear kernels have the same unconditioned and sector Gram
# matrices. Prime freezing and all corresponding PSD inequalities are
# identities of the same marks, not independent matrix assignments.
functions = ((1, 0, 0, 0), (1, 1, 2, 3), (0, -1, 2, 1), (2, 3, -2, 1))

def kernel(f, b):
    return f[0] - sum(f[j + 1] * b[j] for j in range(3))


gram_checks = 0
for f, g in product(functions, repeat=2):
    uncond = Q(sum(kernel(f, b) * kernel(g, b) for b in BITS), 8)
    for sector in (0, 1):
        assert Q(sum(kernel(f, b) * kernel(g, b) for b in SECTORS[sector]), 4) == uncond
        gram_checks += 1
for coeffs in product((-1, 0, 1), repeat=len(functions)):
    vals = [sum(c * kernel(f, b) for c, f in zip(coeffs, functions)) for b in BITS]
    # Conditional-even prime atom is 1/4, so its removal stays PSD.
    residual = Q(sum(vals[BITS.index(b)] ** 2 for b in SECTORS[0]), 4) - Q(vals[0] ** 2, 4)
    assert residual >= 0

# Full observations are NOT in the tested moment algebra: the void
# needs degree 3, and distinguishes the sectors. This is the exact
# failed conditional-independence extension.
void_prob = Q(sum(flags[2] for _, flags in rows), len(rows))
cross_void = Q(sum(flags[0] * flags[2] for _, flags in rows), len(rows))
assert void_prob == Q(1, 8) and cross_void == 0
assert Q(1, 8) * void_prob == Q(1, 64)

# Sobolev atom-capacity check for f(t)=(1-t/a)_+: c=1/a.
for a in (Q(1, 8), Q(1, 4), Q(1, 3), Q(1, 2)):
    assert 1 / a - 2 >= 0
assert 1 / Q(3, 5) - 2 < 0

print(f"PASS: {len(rows)} common rows; {len(mass)} mass and {len(first)} one-prime moments;")
print(f"      {patterns} prime patterns; {gram_checks} mixed Gram entries; 81 PSD checks;")
print("      full-observation conditioning fails exactly: 0 != 1/64.")
print("Finite parity analogue only; no arithmetic asymptotic or prime-gap claim.")
