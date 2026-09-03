import Submission.TranslatedMixedFiberExplore
import Submission.OddExtensionFlatSetExplore

/-! A low-character-energy parameter block can be chosen while avoiding a
prescribed old field. This is a finite-field extension lemma, not a
natural-number representation limit. -/
namespace Erdos66GrowingParameterTranslate
open Erdos66TranslatedCharacterEnergy Erdos66CharacterTranslateSelection
  Erdos66TranslatedMixedFiber Erdos66CrossGraph Erdos66FiniteField
open scoped Classical
set_option maxHeartbeats 2400000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def forbiddenTranslate (R W S : Finset F) : Finset F :=
  ((R.product W).image (fun rw ↦ rw.1-rw.2)) ∪
    (S.image (fun s ↦ -s/2))

omit [Fintype F] in
lemma forbiddenTranslate_card (R W S : Finset F) :
    (forbiddenTranslate R W S).card ≤ R.card*W.card+S.card := by
  unfold forbiddenTranslate
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add (Finset.card_image_le.trans_eq (Finset.card_product R W))
    Finset.card_image_le

omit [Fintype F] in
lemma translated_avoids (R W S : Finset F) (a : F)
    (ha : a ∉ forbiddenTranslate R W S) :
    Disjoint (W.image (fun w ↦ a+w)) R := by
  rw [Finset.disjoint_left]
  intro x hx hR
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
  apply ha
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨(a+w,w),Finset.mem_product.mpr ⟨hR,hw⟩,by simp⟩

omit [Fintype F] in
lemma translated_no_opposites (hF : ringChar F ≠ 2) (R W S : Finset F)
    (hS : ∀ x∈W, ∀ y∈W, x+y∈S) (a : F)
    (ha : a ∉ forbiddenTranslate R W S) :
    ∀ x∈W.image (fun w ↦ a+w), ∀ y∈W.image (fun w ↦ a+w), x+y≠0 := by
  intro x hx y hy he
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
  apply ha
  apply Finset.mem_union_right
  refine Finset.mem_image.mpr ⟨u+v,hS u hu v hv,?_⟩
  apply (div_eq_iff (Ring.two_ne_zero hF)).mpr
  linear_combination -he

/-- The old forbidden set may be a whole embedded subfield. The cost of
avoiding it is explicit; the character-energy constant is unchanged. -/
theorem exists_avoiding_parameter_block (hF : ringChar F ≠ 2)
    (R W S : Finset F) (hS : ∀ x∈W, ∀ y∈W, x+y∈S)
    (hsize : 2*(R.card*W.card+S.card) < Fintype.card F) :
    ∃ V : Finset F, V.card=W.card ∧ Disjoint V R ∧
      (∀ x∈V, ∀ y∈V, x+y≠0) ∧
      (∑ z : F, |(charFiber V z : ℝ)|)^2 ≤ 8*S.card*(W.card:ℝ)^2 := by
  have hD : 2*(forbiddenTranslate R W S).card < Fintype.card F := by
    have hh := forbiddenTranslate_card R W S
    omega
  have hav : (∑ a : F, (translatedEnergy W a : ℝ)) ≤
      (Fintype.card F:ℝ)*(4*(W.card:ℝ)^2) := by
    have hh := average_translated_energy hF W
    exact_mod_cast (by nlinarith only [hh] :
      (∑ a : F, translatedEnergy W a) ≤
        (Fintype.card F:ℤ)*(4*(W.card:ℤ)^2))
  obtain ⟨a,ha,henergy⟩ := exists_small_outside (forbiddenTranslate R W S)
    (fun a ↦ (translatedEnergy W a : ℝ)) (4*(W.card:ℝ)^2) hD
    (fun a ↦ by
      change (0:ℝ) ≤ (translatedEnergy W a:ℝ)
      exact_mod_cast translatedEnergy_nonneg W a) hav
  let V := W.image (fun w ↦ a+w)
  let T := S.image (fun s ↦ a+a+s)
  have hT : T.card=S.card := Finset.card_image_of_injective _ (add_right_injective _)
  have hs : ∀ x∈V, ∀ y∈V, x+y∈T := by
    intro x hx y hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨u+v,hS u hu v hv,by ring⟩
  refine ⟨V,Finset.card_image_of_injective _ (add_right_injective a),
    translated_avoids R W S a ha,translated_no_opposites hF R W S hS a ha,?_⟩
  have hh := crossCharFiber_l1_sq_le V V T hs
  rw [hT,energy_signed_translate] at hh
  have hm := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg (α:=ℝ) S.card)
  change (∑ z : F, |(crossCharFiber V V z:ℝ)|)^2 ≤ _
  nlinarith only [hh,hm]

lemma crossCharFiber_l1_le (U V : Finset F) :
    (∑ z : F, |crossCharFiber U V z|) ≤ (U.card:ℤ)*V.card := by
  calc
    _ ≤ ∑ z : F, ∑ u∈U, ∑ v∈V,
        |if u+v=z then quadraticChar F u*quadraticChar F v else 0| := by
      apply Finset.sum_le_sum
      intro z hz
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun u hu ↦ Finset.abs_sum_le_sum_abs _ _))
    _ = ∑ u∈U, ∑ v∈V, |quadraticChar F u*quadraticChar F v| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
      simp only [apply_ite abs,abs_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    _ ≤ ∑ _u∈U, ∑ _v∈V, (1:ℤ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      rw [abs_mul]
      exact (mul_le_mul (quadraticChar_abs_le_one u) (quadraticChar_abs_le_one v)
        (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    _ = _ := by simp

lemma charFiber_union (U V : Finset F) (hUV : Disjoint U V) (z : F) :
    charFiber (U∪V) z = charFiber U z + charFiber V z +
      crossCharFiber U V z + crossCharFiber V U z := by
  simp only [charFiber,crossCharFiber,Finset.sum_union hUV,Finset.sum_add_distrib]
  ring

/-- Enlarging a parameter set has a field-size-independent cross cost. -/
lemma charFiber_union_l1 (U V : Finset F) (hUV : Disjoint U V) :
    (∑ z : F, |charFiber (U∪V) z|) ≤
      (∑ z : F, |charFiber U z|)+(∑ z : F, |charFiber V z|)+
        2*(U.card:ℤ)*V.card := by
  have hp (z : F) : |charFiber (U∪V) z| ≤
      |charFiber U z|+|charFiber V z|+|crossCharFiber U V z|+
        |crossCharFiber V U z| := by
    rw [charFiber_union U V hUV]
    have h₁ := abs_add_le (charFiber U z) (charFiber V z)
    have h₂ := abs_add_le (charFiber U z+charFiber V z) (crossCharFiber U V z)
    have h₃ := abs_add_le (charFiber U z+charFiber V z+crossCharFiber U V z)
      (crossCharFiber V U z)
    linarith
  have hh := Finset.sum_le_sum (fun z (_ : z∈(Finset.univ:Finset F)) ↦ hp z)
  simp only [Finset.sum_add_distrib] at hh
  have h₁ := crossCharFiber_l1_le U V
  have h₂ := crossCharFiber_l1_le V U
  nlinarith only [hh,h₁,h₂]

end Erdos66GrowingParameterTranslate
