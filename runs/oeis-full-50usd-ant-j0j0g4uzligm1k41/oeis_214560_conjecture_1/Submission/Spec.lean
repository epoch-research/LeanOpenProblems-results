import FormalConjectures.Util.ProblemImports

/--
A214560: Number of 0's in binary expansion of $n^2$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    (Nat.digits 2 (n ^ 2)).count 0

/-!
### Analysis of the conjecture

The statement `∀ x, ∃ i, ∀ n, i < n → a n > x` asserts that the number of binary
zeros of `n ^ 2` tends to infinity, equivalently that for every `x` the set
`{n | a n ≤ x}` is finite.

This is a genuinely deep Diophantine statement:

* `a n ≤ 0` forces `n ^ 2 = 2 ^ L - 1`, i.e. `n ^ 2 + 1 = 2 ^ L`, giving only `n = 1`.
* `a n ≤ 1` is elementary (a `2`-adic valuation argument: the one-zero shapes reduce
  to `n ^ 2 = 2 ^ L - 2` (impossible, `v₂` odd) and `n ^ 2 + 3 = 2 ^ L` (impossible
  mod `8`)).
* `a n ≤ 2` already contains the family `n ^ 2 = 2 ^ L - 7`, i.e. the **Ramanujan–Nagell
  equation** `x ^ 2 + 7 = 2 ^ n`, whose complete solution set `{1, 3, 5, 11, 181}`
  is Nagell's theorem (arithmetic of `ℤ[(1+√-7)/2]`).  This case admits *no* elementary
  (congruence-only) proof: the equation is 2-adically consistent for every `L`.
* `a n ≤ 3` already contains the two-parameter exponential equation
  `n ^ 2 + 2 ^ p + 7 = 2 ^ L`, whose finiteness needs Baker's theory of linear forms
  in logarithms.
* The general case is the uniform finiteness of perfect squares of the shape
  `2 ^ L - 1 - (sum of ≤ x powers of 2)`, a consequence of the **Subspace Theorem**
  (Corvaja–Zannier); no elementary argument is known and Mathlib contains none of the
  required machinery (no Ramanujan–Nagell, no Baker, no Subspace Theorem).

The proof below carries out the *correct* reduction of the conjecture to the finiteness
of `{n | a n ≤ x}`.  The single remaining step `hfin` is exactly this open Diophantine
finiteness.
-/

/-- Conjecture: for every x>=0 there is an i such that a(n)>x for n>i. -/
theorem oeis_214560_conjecture_1 : ∀ (x : ℕ), ∃ (i : ℕ), ∀ (n : ℕ), i < n → a n > x := by
  intro x
  -- It suffices to know that only finitely many `n` have `a n ≤ x`.
  have hfin : {n : ℕ | a n ≤ x}.Finite := by
    sorry
  -- From finiteness, take an upper bound `i`; every `n > i` then satisfies `a n > x`.
  obtain ⟨i, hi⟩ := hfin.bddAbove
  refine ⟨i, fun n hn => ?_⟩
  by_contra h
  push_neg at h
  exact absurd (hi (show n ∈ {n : ℕ | a n ≤ x} from h)) (by omega)
