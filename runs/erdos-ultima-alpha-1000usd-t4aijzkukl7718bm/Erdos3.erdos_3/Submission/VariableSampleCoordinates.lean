import Submission.WeightedFeatureErrors

/-! Lipschitz sampling maps with a separate sample count in each coordinate.
The total phase count is a sum, while the Lipschitz cost remains the sum of
feature weights and is independent of the sample counts. -/
namespace Erdos3VariableSampleCoordinates
open Finset Erdos3FeatureLipschitzEnvelope
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {I : Type*} [Fintype I]

noncomputable def sampleMap (M : I → ℕ) (c : (i : I) → Fin (M i) → ℂ)
    (v : (Σ i : I, Fin (M i)) → ℂ) (i : I) : ℝ :=
  𝔼 j : Fin (M i), (c i j*conj (v ⟨i,j⟩)).re

lemma sampleMap_coordinate_bound (M : I → ℕ) (hM : ∀ i, 0 < M i)
    (c : (i : I) → Fin (M i) → ℂ) (hc : ∀ i j, ‖c i j‖ ≤ 1)
    (v u : (Σ i : I, Fin (M i)) → ℂ) (i : I) :
    |sampleMap M c v i-sampleMap M c u i| ≤ ‖v-u‖ := by
  letI : NeZero (M i) := ⟨Nat.ne_of_gt (hM i)⟩
  unfold sampleMap
  rw [← expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply expect_le univ_nonempty
  intro j _
  calc
    _ = |(c i j*conj (v ⟨i,j⟩-u ⟨i,j⟩)).re| := by rw [map_sub,mul_sub,Complex.sub_re]
    _ ≤ ‖c i j*conj (v ⟨i,j⟩-u ⟨i,j⟩)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖v ⟨i,j⟩-u ⟨i,j⟩‖ := by
      rw [norm_mul,Complex.norm_conj]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc i j) (norm_nonneg _)
    _ ≤ ‖v-u‖ := norm_le_pi_norm (v-u) ⟨i,j⟩

lemma sampleMap_lipschitz (M : I → ℕ) (hM : ∀ i, 0 < M i)
    (c : (i : I) → Fin (M i) → ℂ) (hc : ∀ i j, ‖c i j‖ ≤ 1) :
    LipschitzWith 1 (sampleMap M c) := by
  apply LipschitzWith.of_dist_le_mul
  intro v u
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact sampleMap_coordinate_bound M hM c hc v u i

lemma weighted_factor_lipschitz (w : I → NNReal) (Φ : (I → ℝ) → ℝ)
    (hΦ : ∀ v u, |Φ v-Φ u| ≤ weightedDistance w v u) :
    LipschitzWith (∑ i : I, w i) Φ := by
  apply LipschitzWith.of_dist_le_mul
  intro v u
  simp only [dist_eq_norm,NNReal.coe_sum]
  exact (hΦ v u).trans (weightedDistance_norm_le w v u)

noncomputable def sampledFactor (M : I → ℕ) (c : (i : I) → Fin (M i) → ℂ)
    (Φ : (I → ℝ) → ℝ) (v : (Σ i : I, Fin (M i)) → ℂ) : ℝ := Φ (sampleMap M c v)

lemma sampledFactor_bounds (M : I → ℕ) (c : (i : I) → Fin (M i) → ℂ)
    (Φ : (I → ℝ) → ℝ) (hΦ : ∀ v, 0 ≤ Φ v ∧ Φ v ≤ 1)
    (v : (Σ i : I, Fin (M i)) → ℂ) :
    0 ≤ sampledFactor M c Φ v ∧ sampledFactor M c Φ v ≤ 1 := hΦ _

lemma sampledFactor_lipschitz (M : I → ℕ) (hM : ∀ i, 0 < M i)
    (c : (i : I) → Fin (M i) → ℂ) (hc : ∀ i j, ‖c i j‖ ≤ 1)
    (w : I → NNReal) (Φ : (I → ℝ) → ℝ)
    (hΦ : ∀ v u, |Φ v-Φ u| ≤ weightedDistance w v u) :
    LipschitzWith (∑ i : I, w i) (sampledFactor M c Φ) := by
  simpa only [mul_one] using (weighted_factor_lipschitz w Φ hΦ).comp (sampleMap_lipschitz M hM c hc)

lemma phase_count (M : I → ℕ) : Fintype.card (Σ i : I, Fin (M i)) = ∑ i : I, M i := by simp

#print axioms sampleMap_lipschitz
#print axioms sampledFactor_lipschitz
end Erdos3VariableSampleCoordinates
