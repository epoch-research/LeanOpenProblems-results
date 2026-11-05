import FormalConjecturesUtil

/-!
# Finite representation sets for sums of two cubes

Definitions for the ordered cube-root pairs, unordered pairs, and the exact
constrained-divisor count associated with the problem.
-/

namespace Erdos829Aux

/-- Perfect cubes; definitionally the same set as in the problem statement. -/
def cubes : Set ℕ := {n | ∃ k, k ^ 3 = n}

/-- Ordered pairs of cube roots whose cubes have sum `n`. -/
def rootPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun p => p.1 ^ 3 + p.2 ^ 3 = n)

/-- One ordered representative of each unordered representation. -/
def unorderedPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (rootPairs n).filter (fun p => p.1 ≤ p.2)

/-- Divisors passing the exact discriminant and parity conditions for a sum of cubes. -/
noncomputable def constrainedDivisors (n : ℕ) : Finset ℕ := by
  classical
  exact n.divisors.filter (fun s =>
    ∃ t ∈ Finset.range (s + 1), t % 2 = s % 2 ∧
      4 * n = s * (s ^ 2 + 3 * t ^ 2))

end Erdos829Aux
