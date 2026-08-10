import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A219838: Number of ways to write $n$ as $x + y$ with $0 < x \le y$ and $(xy)^2 + xy + 1$ prime.
The constraints $x+y=n$, $0 < x \le y$ are equivalent to $1 \le x \le n/2$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 (n / 2)).sum fun x : ℕ =>
    let xy_prod := x * (n - x)
    if Nat.Prime (xy_prod ^ 2 + xy_prod + 1) then 1 else 0


/--
Conjecture: a(n) > 0 for all n > 1.
-/
theorem oeis_219838_conjecture_0 : ∀ (n : ℕ), n > 1 → a n > 0 := by
  sorry
