import Submission.RelativeDiscrepancyTransfer

/-! Exact-type and permitted-axiom audit of the conditional discrepancy transfer. -/

open Nat Filter Asymptotics
open Erdos821 Erdos821.AnalyticSieve Erdos821.HigherDivisors

example (k : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, nonprimeMangoldtMoment (k+1) X ≤ c*(X : ℝ) :=
  eventually_nonprimeMangoldtMoment_le_linear k c hc

example (H : ∀ r : ℕ, 1 ≤ r → ∀ t : ℕ, 2 ≤ t →
    (fun L : ℕ => divisorProgressionError r (momentScaleX t L) (momentScaleX t L))
      =o[atTop] (fun L : ℕ =>
        (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^r)) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_of_relative_discrepancy H

#print axioms eventually_nonprimeMangoldtMoment_le_linear
#print axioms tendsto_momentScale_exponent
#print axioms tendsto_momentScaleX
#print axioms eventually_momentScale_mangoldt_five_eighths
#print axioms shiftedPrimeMoment_lower_of_relative_errors
#print axioms eventually_sharp_moment_of_relative_discrepancy
#print axioms sharp_dyadic_moments_of_relative_discrepancy
#print axioms erdos_821_of_relative_discrepancy
