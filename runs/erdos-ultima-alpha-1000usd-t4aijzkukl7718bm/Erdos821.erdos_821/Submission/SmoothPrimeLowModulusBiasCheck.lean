import Submission.SmoothPrimeLowModulusBias

/-! Independent axiom audit for SmoothPrimeLowModulusBias. -/

#print axioms Erdos821.AnalyticSieve.log_dyadic_nat
#print axioms Erdos821.AnalyticSieve.dyadic_log_small_input_error
#print axioms Erdos821.AnalyticSieve.eventually_smooth_low_modulus_bias
#print axioms Erdos821.AnalyticSieve.supplied_smooth_cutoff_below_half
#print axioms Erdos821.AnalyticSieve.eventually_supplied_smooth_cutoff_bias
#print axioms Erdos821.AnalyticSieve.not_supplied_smooth_cutoff_relative_decay

open Nat Filter
open Erdos821.AnalyticSieve
example : ¬(∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
    let N := cofactorScale 100005 (2*m)
    let Y := cofactorScale 44425 (2*m)
    let f := smoothMangoldtWeight N Y
    primeOnlyRestrictedError f Y N ≤ η*restrictedMass f N) :=
  not_supplied_smooth_cutoff_relative_decay
