import Submission.PrimeDivisorLocalFactors

/-! Type and axiom audits for the normalized prime-local moment factors. -/

open Filter
open scoped BigOperators Topology
open Erdos821.HigherDivisors

example (d : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → p.Prime) :
    Tendsto (fun k : ℕ => (k : ℝ)^d *
      (∏ p ∈ P k, (1+(1-(1-1/(p : ℝ))^k)/((p : ℝ)-1)))*ρ^k)
      atTop (𝓝 0) :=
  tendsto_primeDivisorLocalFactor_product_geometric d ρ hρ hρ1 P hP

example (θ : ℝ) (hθ : 1/2 < θ) (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → p.Prime) :
    ∀ᶠ k : ℕ in atTop, ((k : ℝ)+1) *
      (∏ p ∈ P k, (1+(1-(1-1/(p : ℝ))^k)/((p : ℝ)-1)))*(1/2 : ℝ)^k < θ^k :=
  eventually_half_level_local_coefficient_lt θ hθ P hP

#print axioms primeLocalValuationWeight
#print axioms primeDivisorLocalFactor
#print axioms hasSum_primeLocal_divisor
#print axioms normalized_primeLocal_divisor_sum
#print axioms primeDivisorLocalFactor_ge_one
#print axioms primeDivisorLocalFactor_le_quadratic
#print axioms finite_primeDivisorLocalFactor_product_le
#print axioms tendsto_primeDivisorLocalFactor_product_geometric
#print axioms eventually_half_level_local_coefficient_lt
