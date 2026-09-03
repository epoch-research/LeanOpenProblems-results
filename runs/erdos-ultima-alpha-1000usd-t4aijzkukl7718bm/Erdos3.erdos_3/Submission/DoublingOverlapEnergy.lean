import Submission.LocalFactorDimensionReduction

/-! Support-sensitive overlap energy. Small difference doubling, rather
than ambient density, controls the normalized Fourier certificate of a
local character. This avoids a fine-radius/correlation circularity. -/
namespace Erdos3DoublingOverlapEnergy
open Finset Erdos3CorrelationSifting Erdos3CorrelationMoments Erdos3FiniteBohr Erdos3BohrCovering
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma overlap_mean (W : Finset G) : (𝔼 h : G, corr (indicator W) h) = (density W)^2 := by
  unfold corr
  rw [expect_comm]
  have he (x : G) : (𝔼 h : G, indicator W x*indicator W (x+h)) = indicator W x*density W := by
    rw [← mul_expect]
    congr 1
    simpa only [add_comm x] using (expect_translate (indicator W) x).trans (expect_indicator W)
  simp only [he,← expect_mul,expect_indicator,sq]

lemma overlap_support (W : Finset G) (h : G) (hh : h ∉ W-W) : corr (indicator W) h = 0 := by
  apply expect_eq_zero
  intro x _
  by_cases hx : x ∈ W
  · have hxh : x+h ∉ W := by
      intro hx'
      apply hh
      exact mem_sub.mpr ⟨x+h,hx',x,hx,by abel⟩
    simp only [indicator,if_pos hx,if_neg hxh,mul_zero]
  · simp only [indicator,if_neg hx,zero_mul]

lemma overlap_energy_support (W : Finset G) :
    (density W)^4 ≤ density (W-W)*(𝔼 h : G, (corr (indicator W) h)^2) := by
  have he (h : G) : indicator (W-W) h*corr (indicator W) h = corr (indicator W) h := by
    by_cases hh : h ∈ W-W
    · simp only [indicator,if_pos hh,one_mul]
    · simp only [indicator,if_neg hh,overlap_support W h hh,mul_zero]
  have he2 (h : G) : (indicator (W-W) h)^2 = indicator (W-W) h := by
    by_cases hh : h ∈ W-W <;> simp only [indicator,hh,if_true,if_false,one_pow,zero_pow (by decide : 2 ≠ 0)]
  have ht := expect_mul_sq_le_sq_mul_sq univ (indicator (W-W)) (corr (indicator W))
  simp only [he,he2,expect_indicator,overlap_mean] at ht
  convert ht using 1 <;> ring

/-- The factor K is relative difference doubling. No ambient-density inverse
appears in the final energy lower bound. -/
theorem overlap_energy_doubling (W : Finset G) (hW : W.Nonempty) {K : ℝ}
    (hK : ((W-W).card : ℝ) ≤ K*W.card) :
    (density W)^3 ≤ K*(𝔼 h : G, (corr (indicator W) h)^2) := by
  have hd := density_pos W hW
  have hD : density (W-W) ≤ K*density W := by
    unfold density
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hK (Nat.cast_nonneg _)
  have hn : 0 ≤ 𝔼 h : G, (corr (indicator W) h)^2 := expect_nonneg (fun _ _ ↦ sq_nonneg _)
  have he := (overlap_energy_support W).trans (mul_le_mul_of_nonneg_right hD hn)
  nlinarith

lemma bohr_difference_doubling (D : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r) :
    (((bohr D r)-(bohr D r)).card : ℝ) ≤ (81 : ℝ)^D.card*(bohr D r).card := by
  have hsub : bohr D r-bohr D r ⊆ bohr D (2*r) := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_sub.mp hx
    simpa only [sub_eq_add_neg,show r+r = 2*r by ring] using bohr_add ha (bohr_neg hb)
  have ht := (card_le_card hsub).trans (card_double_le D hr)
  exact_mod_cast ht

#print axioms overlap_energy_doubling
#print axioms bohr_difference_doubling
end Erdos3DoublingOverlapEnergy
