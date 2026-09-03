#!/usr/bin/env python3
"""Generate an untrusted potential table; Lean checks all edges with decide +kernel.

Only a no-winding BFS is performed here. The generated table is useful input,
not part of the trusted proof. Regeneration is deterministic and needs Python 3.
"""
from collections import Counter, deque
from pathlib import Path

M = 65
STEPS = ((-1, -1), (-1, 1), (1, -1), (1, 1))

def alive(x, y):
    return all((x + k*y) % p != 0 for k, p in ((2, 5), (-2, 5), (5, 13), (-5, 13)))


def generate():
    vertices = {(x, y) for x in range(M) for y in range(M) if alive(x, y)}
    potentials = {}
    components = Counter()
    edge_count = 0
    for root in sorted(vertices):
        if root in potentials:
            continue
        potentials[root] = (0, 0)
        queue = deque([root])
        size = 0
        while queue:
            u = queue.popleft()
            size += 1
            a, b = potentials[u]
            for dx, dy in STEPS:
                v = ((u[0] + dx) % M, (u[1] + dy) % M)
                if v not in vertices:
                    continue
                edge_count += 1
                proposed = (a + dx, b + dy)
                if v not in potentials:
                    potentials[v] = proposed
                    queue.append(v)
                else:
                    assert potentials[v] == proposed, (u, v, proposed, potentials[v])
        components[size] += 1
    # Independently check the completed potential rather than just BFS tree edges.
    for x, y in vertices:
        for dx, dy in STEPS:
            v = ((x + dx) % M, (y + dy) % M)
            if v in vertices:
                assert potentials[v] == (potentials[x, y][0] + dx, potentials[x, y][1] + dy)
    lines = ['''import Submission.FinitePotential

/-!
# Kernel-checked diagonal-step potential

This generated table concerns the four congruences coming from Gaussian factors
of norms 5 and 13. A BFS on the 65-by-65 quotient supplied the entries. Its
implementation is not trusted: `certificate` checks every allowed edge by
Lean kernel reduction. The quotient has 2304 surviving residues; its largest
component has 580 vertices. No assertion about larger steps is made here.

Regenerate with `python3 Submission/generate_diagonal_certificate.py`.
-/

namespace Erdos952.DiagonalBound

/-- The residue type; parity will be imposed separately on Gaussian primes. -/
abbrev Residue := Fin 65 × Fin 65

/-- Canonical coordinate reduction modulo 65. -/
def reduce (x : ℤ) : Fin 65 :=
  ⟨(x % 65).toNat, by
    have h₀ := Int.emod_nonneg x (by norm_num : (65 : ℤ) ≠ 0)
    have h₁ := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 65)
    omega⟩

/-- Reduction of a Gaussian integer in both coordinates. -/
def residue (z : GaussianInt) : Residue := (reduce z.re, reduce z.im)

/-- The congruence sieve for the four factors `2 ± i`, `3 ± 2i`. -/
def Sieved (r : Residue) : Prop :=
  ((r.1.val : ℤ) + 2 * r.2.val) % 5 ≠ 0 ∧
  ((r.1.val : ℤ) - 2 * r.2.val) % 5 ≠ 0 ∧
  ((r.1.val : ℤ) + 5 * r.2.val) % 13 ≠ 0 ∧
  ((r.1.val : ℤ) - 5 * r.2.val) % 13 ≠ 0

instance (r : Residue) : Decidable (Sieved r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Either coordinate of a diagonal step. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

/-- One of the four diagonal Gaussian steps. -/
def step (u v : Bool) : GaussianInt := ⟨sign u, sign v⟩

/-- A diagonal step reduced modulo 65. -/
def next (r : Residue) (u v : Bool) : Residue :=
  (reduce (r.1.val + sign u), reduce (r.2.val + sign v))

set_option maxRecDepth 100000
set_option maxHeartbeats 0
''']
    for x in range(M):
        vals = [f'⟨{a}, {b}⟩' for y in range(M) for a, b in [potentials.get((x,y), (0,0))]]
        lines.append(f'private def row{x:02d} : Fin 65 → GaussianInt :=\n  ![' + ', '.join(vals) + ']\n')
    lines.append('''/-- An exact lift potential on the finite residue type. Values at deleted
residues are arbitrary (zero). -/
def potential (r : Residue) : GaussianInt :=
  (![''' + ', '.join(f'row{x:02d}' for x in range(M)) + '''] : Fin 65 → Fin 65 → GaussianInt) r.1 r.2

/-- Every sieved diagonal edge has exactly its actual Gaussian displacement.
This proof uses kernel reduction, not native evaluation or compiler trust. -/
theorem certificate : ∀ (a b : Fin 65) (u v : Bool),
    Sieved (a, b) → Sieved (next (a, b) u v) →
    potential (next (a, b) u v) - potential (a, b) = step u v := by
  decide +kernel

end Erdos952.DiagonalBound
''')
    target = Path(__file__).with_name('DiagonalCertificate.lean')
    target.write_text('\n'.join(lines))
    print(f'{target}: {len(vertices)} residues, {edge_count} directed edges, '
          f'{sum(components.values())} components, maximum {max(components)}')
    print('component-size histogram:', dict(sorted(components.items())))

if __name__ == '__main__':
    generate()
