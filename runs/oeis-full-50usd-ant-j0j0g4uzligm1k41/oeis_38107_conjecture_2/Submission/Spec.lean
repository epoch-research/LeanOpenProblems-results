import FormalConjectures.Util.ProblemImports

open Nat

/--
A038107: Number of primes $< n^2$.
This is the cardinality of the set of primes strictly less than $n^2$.
-/
def A038107 (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card

/-
Conjecture: All the numbers Sum_{i=j,...,k} 1/a(i) with 1 < j <= k have pairwise distinct fractional parts.

### Note on this conjecture

This statement provably **implies Legendre's conjecture** (that there is always a prime
between consecutive squares `n²` and `(n+1)²`), which is one of Landau's problems and has
been open since 1808.

Indeed, taking the single-term intervals `j = k = n` and `j' = k' = n+1` (both admissible
for `n ≥ 2`), the two reciprocals `1/A038107 n` and `1/A038107 (n+1)` lie in `(0,1)`, so
their fractional parts equal their values.  The conjecture then forces
`(n,n) = (n+1,n+1)` to fail to be derivable unless the fractional parts differ, i.e. unless
`A038107 n ≠ A038107 (n+1)`.  Since `A038107` is monotone (`Nat.monotone_primeCounting'`),
this means `A038107 n < A038107 (n+1)`, i.e. there is a prime in `[n², (n+1)²)` — exactly
Legendre's conjecture.  This implication is proven completely (no `sorry`) below in
`oeis_38107_conjecture_2_implies_Legendre`.

Mathlib currently contains only Bertrand's postulate (a prime in `(n, 2n]`), which is far
too weak, and no prime-gap result strong enough to yield Legendre's conjecture (which is not
known even under the Riemann Hypothesis).  Consequently a complete formal proof of the
statement below is not attainable with currently-known mathematics; the final step is the
irreducible open number-theoretic input.
-/

/-- Legendre's conjecture, in the form required here: `A038107` is strictly monotone
from `2` onwards.  Equivalently, there is always a prime in `[n², (n+1)²)` for `n ≥ 2`. -/
def LegendreForA : Prop := ∀ n : ℕ, 2 ≤ n → A038107 n < A038107 (n + 1)

/-- `A038107 n ≥ 2` for `n ≥ 2` (there are at least the primes `2, 3` below `n² ≥ 4`). -/
theorem two_le_A038107 (n : ℕ) (hn : 2 ≤ n) : 2 ≤ A038107 n := by
  unfold A038107
  rw [Nat.primesBelow_card_eq_primeCounting']
  calc 2 = Nat.primeCounting' 4 := by decide
    _ ≤ Nat.primeCounting' (n ^ 2) := Nat.monotone_primeCounting' (by nlinarith)

/-- **The conjecture provably implies Legendre's conjecture** (fully verified, no `sorry`). -/
theorem oeis_38107_conjecture_2_implies_Legendre
    (h : let a_inv (i : ℕ) : ℝ := 1 / (A038107 i : ℝ)
         ∀ j k j' k' : ℕ, 1 < j → j ≤ k → 1 < j' → j' ≤ k' →
           Int.fract (Finset.sum (Finset.Icc j k) a_inv)
             = Int.fract (Finset.sum (Finset.Icc j' k') a_inv) → (j, k) = (j', k')) :
    LegendreForA := by
  intro n hn
  have hle : A038107 n ≤ A038107 (n + 1) := by
    unfold A038107
    rw [Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow_card_eq_primeCounting']
    exact Nat.monotone_primeCounting' (by nlinarith)
  rcases lt_or_eq_of_le hle with h1 | h1
  · exact h1
  · exfalso
    have hfract :
        Int.fract (Finset.sum (Finset.Icc n n) (fun i => 1 / (A038107 i : ℝ)))
          = Int.fract (Finset.sum (Finset.Icc (n + 1) (n + 1)) (fun i => 1 / (A038107 i : ℝ))) := by
      rw [Finset.Icc_self, Finset.sum_singleton, Finset.Icc_self, Finset.sum_singleton, h1]
    have hpair := h n n (n + 1) (n + 1) (by omega) (le_refl n) (by omega) (le_refl (n + 1)) hfract
    have : n = n + 1 := (Prod.mk.injEq .. ▸ hpair).1
    omega

theorem oeis_38107_conjecture_2 :
  -- Define the reciprocal function, coercing A038107 i to a real number.
  let a_inv (i : ℕ) : ℝ := 1 / (A038107 i : ℝ)
  -- Iterate over two pairs of indices (j, k) and (j', k')
  ∀ j k j' k' : ℕ,
    -- Constraints 1 < j <= k
    1 < j → j ≤ k →
    -- Constraints 1 < j' <= k'
    1 < j' → j' ≤ k' →
    -- If their fractional parts are equal...
    Int.fract (Finset.sum (Finset.Icc j k) a_inv) = Int.fract (Finset.sum (Finset.Icc j' k') a_inv) →
    -- ...then the index pairs must be identical.
    (j, k) = (j', k') := by
  intro a_inv j k j' k' hj hjk hj' hj'k' hfract
  -- The general case reduces to two open problems: Legendre's conjecture (for single-term
  -- intervals, see `oeis_38107_conjecture_2_implies_Legendre`) together with the arithmetic
  -- distinctness of multi-term reciprocal sums.  Neither is available in current mathematics.
  sorry
