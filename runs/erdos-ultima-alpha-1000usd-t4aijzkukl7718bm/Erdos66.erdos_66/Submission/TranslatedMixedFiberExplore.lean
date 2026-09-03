import Submission.CharacterTranslateSelectionExplore
import Submission.SumDifferenceParametersExplore

/-! Mixed character-fiber bounds obtained from the additive translation
energy estimate, without prescribing a Legendre-symbol pattern. -/
namespace Erdos66TranslatedMixedFiber
open Erdos66CharacterTranslateSelection Erdos66TranslatedCharacterEnergy
  Erdos66CrossGraph Erdos66PolynomialMixedEnergy Erdos66MixedEnergy
  Erdos66DifferenceSignEnergy
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma translatedFiber_double (U : Finset F) (a z : F) :
    translatedFiber U a z = ∑ x ∈ U, ∑ y ∈ U,
      if x+y=z then quadraticChar F (a+x)*quadraticChar F (a+y) else 0 := by
  unfold translatedFiber sumFiber
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  have he (y : F) : x+y=z ↔ y=z-x := by constructor <;> intro h <;> linear_combination h
  simp_rw [he]
  simp only [Finset.sum_ite_eq']

lemma crossCharFiber_translate (U V : Finset F) (a z : F) :
    crossCharFiber (U.image (fun x ↦ a+x)) (V.image (fun y ↦ a+y)) (a+a+z) =
      ∑ x ∈ U, ∑ y ∈ V,
        if x+y=z then quadraticChar F (a+x)*quadraticChar F (a+y) else 0 := by
  unfold crossCharFiber
  rw [Finset.sum_image (fun _ _ _ _ h ↦ add_left_cancel h)]
  simp_rw [Finset.sum_image (fun _ _ _ _ h ↦ add_left_cancel h)]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  apply propext
  constructor <;> intro h <;> linear_combination h

noncomputable def signedFunction (U : Finset F) : F → ℝ :=
  finitePush U id (fun x ↦ (quadraticChar F x : ℝ))

lemma signedFunction_apply (U : Finset F) (x : F) :
    signedFunction U x = if x∈U then (quadraticChar F x : ℝ) else 0 := by
  simp [signedFunction,finitePush]

lemma conv_signedFunction (U V : Finset F) (z : F) :
    conv (signedFunction U) (signedFunction V) z = (crossCharFiber U V z : ℝ) := by
  rw [signedFunction,signedFunction,conv_finitePush]
  simp only [id_eq,crossCharFiber,Int.cast_sum,Int.cast_ite,Int.cast_mul,Int.cast_zero]

lemma energy_signed_translate (U : Finset F) (a : F) :
    energy (signedFunction (U.image (fun x ↦ a+x)))
      (signedFunction (U.image (fun x ↦ a+x))) = (translatedEnergy U a : ℝ) := by
  unfold energy
  simp_rw [conv_signedFunction]
  rw [← Equiv.sum_comp (Equiv.addLeft (a+a))]
  simp only [Equiv.coe_addLeft,crossCharFiber_translate,← translatedFiber_double]
  simp only [translatedEnergy,Int.cast_sum,Int.cast_pow]

omit [DecidableEq F] in
lemma mixed_energy_le_general {f g : F → ℝ} {C h k : ℝ}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hf : energy f f ≤ C*h^2) (hg : energy g g ≤ C*k^2) :
    energy f g ≤ C*h*k := by
  have hs := mixed_energy_sq_le f g
  have hm := mul_le_mul hf hg (energy_nonneg g g) (by positivity : 0 ≤ C*h^2)
  have he := energy_nonneg f g
  have hz : 0 ≤ C*h*k := by positivity
  nlinarith [sq_nonneg (energy f g-C*h*k)]

lemma signedFunction_neg (U : Finset F) (x : F) :
    signedFunction (U.image Neg.neg) x =
      (quadraticChar F (-1) : ℝ)*reflect (signedFunction U) x := by
  rw [signedFunction_apply,reflect,signedFunction_apply]
  have hm : x ∈ U.image Neg.neg ↔ -x ∈ U := by
    constructor
    · rintro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      simpa only [neg_neg] using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨-x,hx,neg_neg x⟩
  simp only [hm]
  split_ifs with hx
  · rw [← Int.cast_mul,← map_mul,neg_one_mul,neg_neg]
  · simp

omit [DecidableEq F] in
lemma conv_scale_right (f g : F → ℝ) (c : ℝ) (z : F) :
    conv f (fun x ↦ c*g x) z = c*conv f g z := by
  unfold conv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma energy_signed_neg_right (U V : Finset F) :
    energy (signedFunction U) (signedFunction (V.image Neg.neg)) =
      energy (signedFunction U) (signedFunction V) := by
  have he : signedFunction (V.image Neg.neg) =
      fun x ↦ (quadraticChar F (-1) : ℝ)*reflect (signedFunction V) x :=
    funext (signedFunction_neg V)
  rw [he]
  unfold energy
  simp_rw [conv_scale_right,mul_pow]
  rw [← Finset.mul_sum]
  have hc : (quadraticChar F (-1) : ℝ)^2=1 := by
    exact_mod_cast quadraticChar_sq_one (F := F) (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
  rw [hc,one_mul]
  exact energy_reflect_right _ _

lemma crossCharFiber_zero_off (U V S : Finset F)
    (hs : ∀ x∈U, ∀ y∈V, x+y ∈ S) (z : F) (hz : z ∉ S) :
    crossCharFiber U V z = 0 := by
  unfold crossCharFiber
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply if_neg
  intro he
  exact hz (he ▸ hs x hx y hy)

lemma crossCharFiber_l1_sq_le (U V S : Finset F)
    (hs : ∀ x∈U, ∀ y∈V, x+y∈S) :
    (∑ z : F, |(crossCharFiber U V z : ℝ)|)^2 ≤
      (S.card : ℝ)*energy (signedFunction U) (signedFunction V) := by
  have hh := l1_sq_le_support_energy (fun z ↦ (crossCharFiber U V z : ℝ)) S
    (fun z hz ↦ by change (crossCharFiber U V z : ℝ) = 0; rw [crossCharFiber_zero_off U V S hs z hz,Int.cast_zero])
  simpa only [energy,conv_signedFunction] using hh

noncomputable def sumSupport (p : ℕ) (a : ZMod p) (h k : ℕ) : Finset (ZMod p) :=
  (Finset.range (h+k)).image (fun i : ℕ ↦ a+a+(i : ZMod p))

lemma sumSupport_card (p : ℕ) (a : ZMod p) (h k : ℕ) :
    (sumSupport p a h k).card ≤ h+k := by
  unfold sumSupport
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

lemma interval_sum_mem_support (p : ℕ) (a : ZMod p) (h k : ℕ)
    (x : ZMod p) (hx : x∈intervalTranslate p a h)
    (y : ZMod p) (hy : y∈intervalTranslate p a k) : x+y∈sumSupport p a h k := by
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
  apply Finset.mem_image.mpr
  refine ⟨i+j,Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; have := Finset.mem_range.mp hj; omega),?_⟩
  push_cast
  ring

lemma interval_diff_mem_support (p : ℕ) [NeZero p] (a : ZMod p) (h k : ℕ)
    (x : ZMod p) (hx : x∈intervalTranslate p a h)
    (y : ZMod p) (hy : y∈(intervalTranslate p a k).image Neg.neg) :
    x+y∈differenceSupport p h k := by
  obtain ⟨ny,hny,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hny
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
  apply Finset.mem_image.mpr
  refine ⟨(i : ℤ)-j,?_,?_⟩
  · have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    simp only [Finset.mem_Icc]
    omega
  · push_cast
    ring

lemma interval_mixed_l1_sq {p : ℕ} [Fact p.Prime] (a : ZMod p) (h k : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hh : (translatedEnergy (baseInterval p h) a : ℝ) ≤ C*(h : ℝ)^2)
    (hk : (translatedEnergy (baseInterval p k) a : ℝ) ≤ C*(k : ℝ)^2) :
    (∑ z : ZMod p, |(crossCharFiber (intervalTranslate p a h) (intervalTranslate p a k) z : ℝ)|)^2 ≤
      C*h*k*(h+k) ∧
    (∑ z : ZMod p, |(crossCharFiber (intervalTranslate p a h)
      ((intervalTranslate p a k).image Neg.neg) z : ℝ)|)^2 ≤ C*h*k*(h+k+1) := by
  have hh' : energy (signedFunction (intervalTranslate p a h))
      (signedFunction (intervalTranslate p a h)) ≤ C*(h : ℝ)^2 := by
    rw [intervalTranslate,energy_signed_translate]
    exact hh
  have hk' : energy (signedFunction (intervalTranslate p a k))
      (signedFunction (intervalTranslate p a k)) ≤ C*(k : ℝ)^2 := by
    rw [intervalTranslate,energy_signed_translate]
    exact hk
  have he := mixed_energy_le_general hC (Nat.cast_nonneg h) (Nat.cast_nonneg k) hh' hk'
  constructor
  · have hb := crossCharFiber_l1_sq_le (intervalTranslate p a h) (intervalTranslate p a k)
      (sumSupport p a h k) (interval_sum_mem_support p a h k)
    have hcard : ((sumSupport p a h k).card : ℝ) ≤ (h : ℝ)+k := by
      exact_mod_cast sumSupport_card p a h k
    have hm := mul_le_mul hcard he (energy_nonneg _ _) (by positivity : 0 ≤ (h : ℝ)+k)
    nlinarith
  · have hb := crossCharFiber_l1_sq_le (intervalTranslate p a h) ((intervalTranslate p a k).image Neg.neg)
      (differenceSupport p h k) (interval_diff_mem_support p a h k)
    rw [energy_signed_neg_right] at hb
    have hcard : ((differenceSupport p h k).card : ℝ) ≤ (h : ℝ)+k+1 := by
      exact_mod_cast differenceSupport_card p h k
    have hm := mul_le_mul hcard he (energy_nonneg _ _) (by positivity : 0 ≤ (h : ℝ)+k+1)
    nlinarith

end Erdos66TranslatedMixedFiber
