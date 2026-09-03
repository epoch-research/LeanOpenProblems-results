#!/usr/bin/env python3
"""Independent symbolic/numerical checks; no assertion about prime correlations."""
import hashlib
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps = 60
eta = mp.mpf(1) / 8
a2 = mp.log(7)
a3 = mp.quad(
    lambda t: mp.log((1 - t - eta) / eta) / (3 * t * (1 - t)),
    [eta, mp.mpf(1) / 2, 1 - 2 * eta],
)
lower_a3 = mp.log(3) * mp.log(7) / 3
assert a2 > mp.mpf(3) / 2
assert a3 >= lower_a3 > mp.mpf(1) / 2

v = sp.Matrix([2, -3, 1])
perturbation = -v * v.T / 4
assert perturbation * sp.ones(3, 1) == sp.zeros(3, 1)
assert perturbation * sp.Matrix([2, 4, 8]) == sp.zeros(3, 1)
assert perturbation[0, 0] == -1

z, w = sp.symbols('z w')
poly = sum(perturbation[i, j] * z**(i+1) * w**(j+1)
           for i in range(3) for j in range(3))
assert sp.expand(poly + z*(z-1)*(z-2)*w*(w-1)*(w-2)/4) == 0
for variable in [z, w]:
    for value in [0, 1, 2]:
        assert sp.expand(poly.subs(variable, value)) == 0

masses = [mp.mpf(1), a2, a3]
table = [[masses[i] * masses[j] - mp.mpf(int(v[i])) * int(v[j]) / 4
          for j in range(3)] for i in range(3)]
assert table[0][0] == 0
assert all(x >= 0 for row in table for x in row)
print('a2 =', mp.nstr(a2, 35))
print('a3 =', mp.nstr(a3, 35))
print('analytic lower bound for a3 =', mp.nstr(lower_a3, 35))
print('perturbation =', perturbation)
print('nonnegative completion:')
for row in table:
    print([mp.nstr(x, 24) for x in row])

spec = Path(__file__).with_name('Spec.lean')
digest = hashlib.sha256(spec.read_bytes()).hexdigest()
expected = '47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123'
assert digest == expected
assert spec.read_text().count('sorry') == 2
print('Spec unchanged, SHA-256:', digest, '; original sorry count: 2')
print('All checks passed. No prime-pair asymptotic was assumed or tested.')
