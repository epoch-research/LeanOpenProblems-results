import Submission.CofinalBoundedRectangleSupply

/-! Expanded prime-output count, same-input mean, and axiom audit. -/
open Nat Finset Filter
open scoped BigOperators Topology
open Erdos821.AnalyticSieve Erdos821.Kloosterman

example (θ β : ℝ)
    (hθ : θ < 4/7) (hβ : β < 1) :
    ∃ k : ℕ, 5 ≤ k ∧ ∀ d : ℕ, ∀ η : ℝ, 0 < η →
      ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^(64*m) < p ∧ p ≤ 2^(128*m) ∧
        ((2^((14*k+16)*(64*m)) : ℕ) : ℝ)^θ < (2^((8*k+4)*(64*m)) : ℕ) ∧
        ((2^((14*k+16)*(64*m)) : ℕ) : ℝ)^β <
          (((((Icc 1 (2^((7*k+7)*(64*m)) : ℕ)) ×ˢ (Icc 1 (2^((7*k+7)*(64*m)) : ℕ))).image (fun ab => ab.1*ab.2*p+1)).filter Nat.Prime)).card ∧
        (∀ R ∈ ((((Icc 1 (2^((7*k+7)*(64*m)) : ℕ)) ×ˢ (Icc 1 (2^((7*k+7)*(64*m)) : ℕ))).image (fun ab => ab.1*ab.2*p+1)).filter Nat.Prime),
          R ≤ (2^((14*k+16)*(64*m)) : ℕ)+1 ∧
          R-1 ∈ Nat.smoothNumbers ((2^((7*k+7)*(64*m)) : ℕ)+1)) ∧
        (2^((14*k+16)*(64*m)) : ℕ)+1 < (2^((8*k+4)*(64*m)) : ℕ)^2 ∧
        ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ (2^((8*k+4)*(64*m)) : ℕ)) →
        (1+Real.log ((2^((14*k+16)*(64*m)) : ℕ) : ℝ))^d*
          (∑ q ∈ P, |(∑ i ∈ range ((2^((7*k+7)*(64*m)) : ℕ)),
            ∑ j ∈ range ((2^((7*k+7)*(64*m)) : ℕ)),
              if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
            ((2^((7*k+7)*(64*m)) : ℕ) : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
          η*((2^((7*k+7)*(64*m)) : ℕ) : ℝ)^2 := by
  simpa only [rectanglePrimeOutputs,parametricInterval,parametricModulus,parametricAmbient]
    using exists_prime_rectangle_supply_above_levels θ β hθ hβ

#print axioms Erdos821.AnalyticSieve.rectanglePrimeOutputs
#print axioms Erdos821.AnalyticSieve.mem_rectanglePrimeOutputs
#print axioms Erdos821.AnalyticSieve.structured_prime_has_rectangle
#print axioms Erdos821.AnalyticSieve.exists_common_prime_rectangle
#print axioms Erdos821.AnalyticSieve.geometricBlockPrimes_card_le_scale
#print axioms Erdos821.AnalyticSieve.eventually_exists_prime_rectangle_supply
#print axioms Erdos821.AnalyticSieve.rectanglePrimeOutputs_pred_smooth
#print axioms Erdos821.AnalyticSieve.eventually_bounded_prime_supply_and_mean
#print axioms Erdos821.AnalyticSieve.exists_parametric_joint_levels
#print axioms Erdos821.AnalyticSieve.parametric_supply_power_gt_rpow
#print axioms Erdos821.AnalyticSieve.exists_prime_rectangle_supply_above_levels
