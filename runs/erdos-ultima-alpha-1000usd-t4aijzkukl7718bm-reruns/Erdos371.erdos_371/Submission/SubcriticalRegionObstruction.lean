import FormalConjecturesUtil
import Submission.RestrictedMoments

/-! The finite selection-moment model remains biased after restriction to
its subcritical largest-part region. This is an abstract obstruction to a
moment-only extraction, NOT an arithmetic counterexample to Erdős 371. -/

namespace Erdos371SubcriticalRegionObstruction

open Finset Erdos371RestrictedMoments

/-- The finite analogue of a largest-prime product cutoff. -/
def lowComparison (i j : State) : ℤ :=
  if largest i + largest j ≤ 5 then
    (if largest i > largest j then 1 else if largest i < largest j then -1 else 0)
  else 0

def strictLowComparison (i j : State) : ℤ :=
  if largest i + largest j < 5 then
    (if largest i > largest j then 1 else if largest i < largest j then -1 else 0)
  else 0

lemma low_weighted_sum :
    (∑ i : State, ∑ j : State, weight i j * lowComparison i j) = 8 := by
  decide +kernel

lemma strict_low_weighted_sum :
    (∑ i : State, ∑ j : State, weight i j * strictLowComparison i j) = -6 := by
  decide +kernel

lemma low_independent_sum :
    (∑ i : State, ∑ j : State, base i * base j * lowComparison i j) = 0 := by
  decide +kernel

lemma low_perturb_sum :
    (∑ i : State, ∑ j : State, perturb i j * lowComparison i j) = 8 := by
  decide +kernel

/-- All pairs of the existing selection features within the mass budget. -/
def features : Finset (List ℕ × List ℕ) :=
  (selections.toFinset.product selections.toFinset).filter
    fun uv => uv.1.sum + uv.2.sum ≤ 5

lemma feature_annihilation {uv : List ℕ × List ℕ} (huv : uv ∈ features) :
    (∑ i : State, ∑ j : State,
      (perturb i j : ℝ) * (feature uv.1 i : ℝ) * (feature uv.2 j : ℝ)) = 0 := by
  obtain ⟨huv, hbudget⟩ := Finset.mem_filter.mp huv
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  have h := subcritical_moments uv.1 (List.mem_toFinset.mp hu)
    uv.2 (List.mem_toFinset.mp hv) hbudget
  have hbase : (∑ i : State, ∑ j : State,
      base i * base j * feature uv.1 i * feature uv.2 j) =
      (∑ i : State, base i * feature uv.1 i) *
        (∑ j : State, base j * feature uv.2 j) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsplit : (∑ i : State, ∑ j : State,
      weight i j * feature uv.1 i * feature uv.2 j) =
      (∑ i : State, ∑ j : State,
        base i * base j * feature uv.1 i * feature uv.2 j) +
      (∑ i : State, ∑ j : State,
        perturb i j * feature uv.1 i * feature uv.2 j) := by
    simp [weight, add_mul, Finset.sum_add_distrib]
  rw [hsplit, hbase] at h
  have hz : (∑ i : State, ∑ j : State,
      perturb i j * feature uv.1 i * feature uv.2 j) = 0 := by omega
  exact_mod_cast hz

/-- In this model, no real linear combination of the subcritical selection
features equals the restricted largest-part comparison pointwise. -/
theorem low_comparison_not_in_feature_span :
    ¬ ∃ c : List ℕ × List ℕ → ℝ, ∀ i j : State,
      (lowComparison i j : ℝ) = ∑ uv ∈ features,
        c uv * (feature uv.1 i : ℝ) * (feature uv.2 j : ℝ) := by
  rintro ⟨c, hc⟩
  have hsum : (∑ i : State, ∑ j : State,
      (perturb i j : ℝ) * (lowComparison i j : ℝ)) = 0 := by
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro uv huv
    have he : (∑ j : State, ∑ i : State,
        (perturb i j : ℝ) *
          (c uv * (feature uv.1 i : ℝ) * (feature uv.2 j : ℝ))) =
        c uv * (∑ i : State, ∑ j : State,
          (perturb i j : ℝ) * (feature uv.1 i : ℝ) * (feature uv.2 j : ℝ)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [he, feature_annihilation huv, mul_zero]
  have hnonzero : (∑ i : State, ∑ j : State,
      (perturb i j : ℝ) * (lowComparison i j : ℝ)) = 8 := by
    exact_mod_cast low_perturb_sum
  linarith

end Erdos371SubcriticalRegionObstruction

#print axioms Erdos371SubcriticalRegionObstruction.low_weighted_sum
#print axioms Erdos371SubcriticalRegionObstruction.strict_low_weighted_sum
#print axioms Erdos371SubcriticalRegionObstruction.low_comparison_not_in_feature_span
