import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma algebra_ineq (p M x : ℕ) (hp5 : 5 ≤ p) (hx : M - p + 3 ≤ x) (hM : p ≤ M) :
  p * M - p * p + 2 * p + 2 ≤ p * x := by
  have H : (p * M - p * p + 2 * p + 2 : ℤ) ≤ (p * x : ℤ) := by
    have hx_z : (M : ℤ) - p + 3 ≤ (x : ℤ) := by zify at hx; exact hx
    have : (p : ℤ) * M - (p : ℤ) * p + 2 * p + 2 ≤ (p : ℤ) * (M - p + 3) := by nlinarith
    have : (p : ℤ) * (M - p + 3) ≤ (p : ℤ) * x := by nlinarith
    linarith
  exact_mod_cast H
