import Submission.TotientHarmonicCutoff

/-! Exact-type and axiom checks for the truncated harmonic totient correction. -/

open Nat Filter
open scoped Topology
open Erdos821.HigherDivisors

example (k A : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Icc 1 A, (tau k n : ℝ)/(n.totient : ℝ)) ≤
      eulerCost k * harmonicMoment k A :=
  totientHarmonicMoment_le_cost k A hk

example (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    Tendsto (fun k : ℕ => ((k+1).factorial : ℝ) * eulerCost k *
      (Real.exp 1 / (k : ℝ))^k * θ^k) atTop (𝓝 0) :=
  tendsto_successor_factorial_totient_cutoff_coefficient θ hθ hθ1

#print axioms totientHarmonicMoment_le_cost
#print axioms totientHarmonicMoment_rankin_normalized
#print axioms tendsto_factorial_totient_cutoff_coefficient
#print axioms tendsto_successor_factorial_totient_cutoff_coefficient
