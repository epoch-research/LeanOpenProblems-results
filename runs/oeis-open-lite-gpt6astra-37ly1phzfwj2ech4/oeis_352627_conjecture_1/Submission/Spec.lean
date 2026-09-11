import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352627: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 4d^4 + c^2d^2$,
where $a, b, c, d$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R)) -- Represents a set of $\mathbb{N}^4$ tuples

  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each
nonnegative integer can be written as a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2 with a,b,c,d integers. -/
theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  sorry

theorem oeis_352627_conjecture_1.disproof : ¬ (type_of% @oeis_352627_conjecture_1) := sorry
