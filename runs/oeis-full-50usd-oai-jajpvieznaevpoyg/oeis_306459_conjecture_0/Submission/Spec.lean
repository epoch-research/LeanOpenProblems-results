import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $k$-th "shifted" tetrahedral number $C(k+2,3) = \binom{k+2}{3}$. -/
def tetrahedral_term (k : ℕ) : ℕ := (k + 2).choose 3

/--
A306459: Number of ways to write $n$ as $w^3 + C(x+2,3) + C(y+2,3) + C(z+2,3)$,
where $w,x,y,z$ are nonnegative integers with $x \le y \le z$.
-/
def A306459 (n : ℕ) : ℕ :=
  let T := tetrahedral_term
  -- A safe upper bound B for all variables w, x, y, z.
  -- Since w³ ≤ n and T(x) ≤ n, the search space can be restricted to {0, ..., n}^4.
  let B : ℕ := n + 1

  (range B).sum fun w =>
    (range B).sum fun x =>
      (range B).sum fun y =>
        (range B).sum fun z =>
          if x ≤ y ∧ y ≤ z ∧ w ^ 3 + T x + T y + T z = n
          then 1 else 0

/--
Conjecture: a(n) > 0 for all n >= 0. In other words, each nonnegative integer
can be written as the sum of a nonnegative cube and three tetrahedral numbers.
-/
theorem oeis_306459_conjecture_0 (n : ℕ) : A306459 n > 0 := by
  sorry
