import Submission.VariableCofactorReciprocals

/-! Type and axiom checks for the variable-cofactor criterion. -/
open Nat Filter
open scoped Classical
namespace Erdos821
example (A : ℕ → ℕ) (hA : Monotone A)
    (hsmall : ∀ᶠ m : ℕ in atTop, A (2^(128*m)) ≤ 2^m)
    (hsum : Summable (fun m : ℕ => (harmonic (A (2^(128*m))) : ℝ)/(m : ℝ)^2)) :
    Summable (({p : ℕ | p ∈ boundedCofactorParentSet (A p)} : Set ℕ).indicator
      (fun p : ℕ => 1/(p : ℝ))) :=
  summable_variable_cofactor_parent_reciprocal A hA hsmall hsum
example (R β : ℝ) (hR : 0 ≤ R) (hβ : 0 ≤ β) (hβ1 : β < 1) :
    Summable (({p : ℕ | p ∈ boundedCofactorParentSet
      (2^⌊R*(Nat.log 2 p : ℝ)^β⌋₊)} : Set ℕ).indicator (fun p : ℕ => 1/(p : ℝ))) :=
  summable_stretchedLog_cofactor_parent_reciprocal R β hR hβ hβ1
example (R β : ℝ) (hR : 0 ≤ R) (hβ : 0 ≤ β) (hβ1 : β < 1) :
    ¬Summable (({p : ℕ | p.Prime ∧ ∀ q ∈ (p-1).primeFactors,
      (2^⌊R*(Nat.log 2 p : ℝ)^β⌋₊)*q < p-1} : Set ℕ).indicator
      (fun p : ℕ => 1/(p : ℝ))) :=
  not_summable_stretchedLog_prime_factor_bound R β hR hβ hβ1
#print axioms variableCofactorParent_count_le
#print axioms summable_variable_cofactor_parent_reciprocal
#print axioms stretchedLogCofactorCutoff_mono
#print axioms eventually_stretchedLog_block_cutoff_le
#print axioms harmonic_stretchedLog_block_le
#print axioms summable_stretchedLog_harmonic_cost
#print axioms summable_stretchedLog_cofactor_parent_reciprocal
#print axioms prime_outside_variable_cofactor_parent_iff
#print axioms not_summable_stretchedLog_prime_factor_bound
example (R : ℝ) (hR : 0 < R) :
    ¬Summable (fun m : ℕ =>
      (harmonic (2^⌊R*(128*(m : ℝ))⌋₊) : ℝ)/(m : ℝ)^2) := by
  simpa only [stretchedLogCofactorCutoff, Nat.log_pow (by decide : 1 < 2),
    Nat.cast_mul, Nat.cast_ofNat, Real.rpow_one] using
      not_summable_linearLog_harmonic_cost R hR
#print axioms not_summable_linearLog_harmonic_cost
end Erdos821
