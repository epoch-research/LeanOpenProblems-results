import Submission.WeightedSparseCompletionExplore
import Submission.SuperquadraticCostsExplore

/-! Superquadratically separated lower-bound exceptions can be repaired.
The base-set existence required for Erdos 66 remains unproved. -/
namespace Erdos66SuperquadraticCompletion
open Filter AdditiveCombinatorics Erdos66ClippedRepair Erdos66WeightedSparseCompletion
  Erdos66SuperquadraticCosts
open scoped Topology Classical

/-- Any fixed exponent strictly greater than two suffices, improving the
previous exponent-twelve sufficient condition. -/
theorem superquadratic_exception_completion (c K C : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (n : ℕ → ℕ) (hn : Function.Injective n) (p : ℝ) (hp : 2 < p)
    (hg : ∀ᶠ k : ℕ in atTop, ((k : ℝ)+1)^p ≤ n k)
    (A : Set ℕ) (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop, (sumRep A z : ℝ) ≤ (c+ε)*logScale z)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      z ∉ Set.range n → (c-ε)*logScale z ≤ (sumRep A z : ℝ)) :
    ∃ B : Set ℕ, A ⊆ B ∧ Tendsto (fun z ↦ (sumRep B z : ℝ)/Real.log z) atTop (𝓝 c) := by
  exact summable_exception_completion c K C hc hK hC n hn
    (weighted_cost_summable p hp n hg) A hA hu hl

/-- A convenient integer-power specialization. -/
theorem cubic_exception_completion (c K C : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (n : ℕ → ℕ) (hn : Function.Injective n) (hg : ∀ᶠ k : ℕ in atTop, (k+1)^3 ≤ n k)
    (A : Set ℕ) (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop, (sumRep A z : ℝ) ≤ (c+ε)*logScale z)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      z ∉ Set.range n → (c-ε)*logScale z ≤ (sumRep A z : ℝ)) :
    ∃ B : Set ℕ, A ⊆ B ∧ Tendsto (fun z ↦ (sumRep B z : ℝ)/Real.log z) atTop (𝓝 c) := by
  apply superquadratic_exception_completion c K C hc hK hC n hn 3 (by norm_num) ?_ A hA hu hl
  filter_upwards [hg] with k hk
  rw [show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_natCast]
  exact_mod_cast hk

end Erdos66SuperquadraticCompletion
