import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352628: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 2d^4 + 3c^2d^2$,
where $a,b,c,d$ are nonnegative integers.
-/
def A352628 (n : ℕ) : ℕ :=
  let S : Finset ℕ := range (n + 1)

  -- The number of ways is the sum of 1 for each tuple that satisfies the equation.
  -- Using nested sums avoids complex tuple unpacking and Finset product issues.
  S.sum fun a =>
    S.sum fun b =>
      S.sum fun c =>
        S.sum fun d =>
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0

/--
Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each nonnegative integer can be written as $a^2 + 2b^2 + (c^2+d^2)(c^2+2d^2)$ with a,b,c,d integers.
-/
theorem oeis_352628_conjecture_0 (n : ℕ) : A352628 n > 0 := by
  sorry
