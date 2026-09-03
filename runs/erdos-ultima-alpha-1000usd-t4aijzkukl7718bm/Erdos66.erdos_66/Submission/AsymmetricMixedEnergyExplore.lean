import Submission.TranslatedMixedFiberExplore

/-! Mixed character bounds using only the SHORTER interval's self-energy.
This avoids a maximum-level cost in highly unbalanced finite families. -/
namespace Erdos66AsymmetricMixedEnergy
open Erdos66MixedEnergy Erdos66TranslatedMixedFiber Erdos66DifferenceSignEnergy
  Erdos66CharacterTranslateSelection Erdos66TranslatedCharacterEnergy Erdos66FiniteField
  Erdos66CrossGraph
open scoped Classical
set_option maxHeartbeats 2200000

section Group
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma asymmetric_energy_sq (f g : G → ℝ) (S : Finset G) (M : ℝ) (hM : 0 ≤ M)
    (hS : ∀ t, t∉S → corr f t=0) (hg : ∀ t, |corr g t| ≤ M) :
    energy f g ^ 2 ≤ M^2*(S.card:ℝ)*energy f f := by
  have hsum : energy f g ≤ M*∑ t, |corr f t| := by
    rw [energy_eq_corr_inner,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    calc
      _ ≤ |corr f t*corr g t| := le_abs_self _
      _ = |corr f t| *|corr g t| := abs_mul _ _
      _ ≤ |corr f t| *M := mul_le_mul_of_nonneg_left (hg t) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hl1 := l1_sq_le_support_energy (corr f) S hS
  have he : (∑ t, (corr f t)^2)=energy f f := by
    rw [energy_eq_corr_inner]
    simp only [pow_two]
  rw [he] at hl1
  have hs := pow_le_pow_left₀ (energy_nonneg f g) hsum 2
  have hh := mul_le_mul_of_nonneg_left hl1 (sq_nonneg M)
  nlinarith only [hs,hh]

end Group

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma signed_abs_le_one (U : Finset F) (x : F) : |signedFunction U x| ≤ 1 := by
  rw [signedFunction_apply]
  split_ifs
  · exact_mod_cast quadraticChar_abs_le_one x
  · norm_num

lemma signed_corr_abs_le_card (U : Finset F) (t : F) :
    |corr (signedFunction U) t| ≤ (U.card:ℝ) := by
  calc
    _ ≤ ∑ x, |signedFunction U x*signedFunction U (x+t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : F, if x∈U then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases h : x∈U
      · rw [if_pos h,abs_mul]
        exact (mul_le_mul (signed_abs_le_one U x) (signed_abs_le_one U (x+t)) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      · simp only [signedFunction_apply U x,h,ite_false,zero_mul,abs_zero,le_refl]
    _ = _ := by simp

lemma signed_corr_zero_off (U S : Finset F)
    (hS : ∀ x∈U, ∀ y∈U, y-x∈S) (t : F) (ht : t∉S) :
    corr (signedFunction U) t=0 := by
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hxU : x∈U
  · have hxt : x+t∉U := by
      intro hh
      have he := hS x hxU (x+t) hh
      exact ht (by simpa only [add_sub_cancel_left] using he)
    simp only [signedFunction_apply U (x+t),hxt,ite_false,mul_zero]
  · simp only [signedFunction_apply U x,hxU,ite_false,zero_mul]

end Field

lemma interval_corr_zero_off (p : ℕ) [Fact p.Prime] (a : ZMod p) (h : ℕ)
    (t : ZMod p) (ht : t∉differenceSupport p h h) :
    corr (signedFunction (intervalTranslate p a h)) t=0 := by
  apply signed_corr_zero_off _ _ ?_ t ht
  intro x hx y hy
  have he := interval_diff_mem_support p a h h y hy (-x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  simpa only [sub_eq_add_neg] using he

lemma interval_mixed_l1_fourth (p : ℕ) [Fact p.Prime] (a : ZMod p) (h k : ℕ)
    (hh : 1 ≤ h) (hhk : h ≤ k) (hk : k ≤ p) :
    (∑ z : ZMod p, |(crossCharFiber (intervalTranslate p a h) (intervalTranslate p a k) z:ℝ)|)^4 ≤
      12*(h:ℝ)*(k:ℝ)^4*(translatedEnergy (baseInterval p h) a:ℝ) := by
  let f := signedFunction (intervalTranslate p a h)
  let g := signedFunction (intervalTranslate p a k)
  have hE := asymmetric_energy_sq f g (differenceSupport p h h) (k:ℝ) (by positivity)
    (interval_corr_zero_off p a h) (fun t ↦ by
      simpa only [intervalTranslate_card p a hk] using signed_corr_abs_le_card (intervalTranslate p a k) t)
  have hcard : ((differenceSupport p h h).card:ℝ) ≤ 3*(h:ℝ) := by
    have hc : ((differenceSupport p h h).card:ℝ) ≤ (h:ℝ)+h+1 := by exact_mod_cast differenceSupport_card p h h
    have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hEf : energy f f=(translatedEnergy (baseInterval p h) a:ℝ) := by
    exact energy_signed_translate (baseInterval p h) a
  have hE' : energy f g ^ 2 ≤ 3*(h:ℝ)*(k:ℝ)^2*(translatedEnergy (baseInterval p h) a:ℝ) := by
    have he0 := energy_nonneg f f
    have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (sq_nonneg (k:ℝ))) he0
    rw [hEf] at hE hbound
    nlinarith only [hE,hbound]
  have hL := crossCharFiber_l1_sq_le (intervalTranslate p a h) (intervalTranslate p a k)
    (sumSupport p a h k) (interval_sum_mem_support p a h k)
  have hcard' : ((sumSupport p a h k).card:ℝ) ≤ 2*(k:ℝ) := by
    have hc : ((sumSupport p a h k).card:ℝ) ≤ (h:ℝ)+k := by exact_mod_cast sumSupport_card p a h k
    have hk' : (h:ℝ) ≤ k := by exact_mod_cast hhk
    linarith
  have hL' := hL.trans (mul_le_mul_of_nonneg_right hcard' (energy_nonneg f g))
  have hsq := pow_le_pow_left₀ (sq_nonneg _) hL' 2
  have he := mul_le_mul_of_nonneg_left hE' (show (0:ℝ) ≤ 4*(k:ℝ)^2 by positivity)
  nlinarith only [hsq,he]

end Erdos66AsymmetricMixedEnergy
