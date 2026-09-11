import FormalConjectures.Util.ProblemImports

open Nat

/--
A273110: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with
$(x+4y+4z)^2 + (9x+3y+3z)^2$ a square, where $x,y,z,w$ are nonnegative integers
with $y > 0$ and $y \ge z \le w$.
-/
def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n -- Safe and conservative upper bound

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

/-- The conductor set M for the conjecture of A273110(n) = 1. -/
def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

/--
OEIS A273110 Conjecture (i):
a(n) > 0 for all n > 0, and a(n) = 1 only for n = 4^k*m (k = 0,1,2,... and
m is in the set {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}).
-/
theorem A273110_conjecture (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) :=
by sorry

theorem A273110_conjecture.disproof : ¬ (type_of% @A273110_conjecture) := sorry
