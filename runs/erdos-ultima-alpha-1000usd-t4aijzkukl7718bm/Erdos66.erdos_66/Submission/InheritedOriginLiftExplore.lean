import Submission.ParabolaOriginInheritanceExplore
import Submission.TranslatedMixedFiberExplore

/-! Translation selection and a finite flatness transfer without a separate
origin repair. The lifted mean is amplified by the field size. -/
namespace Erdos66InheritedOriginLift
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph Erdos66DegenerateCrossGraph
  Erdos66ParabolaOriginInheritance Erdos66TranslatedCharacterEnergy
  Erdos66CharacterTranslateSelection Erdos66TranslatedMixedFiber Erdos66MixedEnergy
open scoped Classical
set_option maxHeartbeats 1800000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def translated (U : Finset F) (a : F) : Finset F := U.image (fun x ↦ a+x)

omit [Fintype F] in
lemma translated_card (U : Finset F) (a : F) : (translated U a).card=U.card :=
  Finset.card_image_of_injective _ (add_right_injective a)

omit [Fintype F] in
lemma pairCount_translated (U V : Finset F) (a b z : F) :
    pairCount (translated U a) (translated V b) z=pairCount U V (z-a-b) := by
  unfold pairCount translated
  rw [Finset.filter_image,Finset.card_image_of_injective _ (add_right_injective a)]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  have he : z-(a+x)∈V.image (fun y ↦ b+y) ↔ z-a-b-x∈V := by
    constructor
    · rintro h
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
      have hy' : y=z-a-b-x := by linear_combination he
      simpa only [hy'] using hy
    · intro h
      exact Finset.mem_image.mpr ⟨z-a-b-x,h,by ring⟩
  rw [he]

lemma exists_nonzero_low_energy_translate (hF : ringChar F≠2) (U : Finset F)
    (hU : 2*U.card<Fintype.card F) :
    ∃ a : F, (∀ u∈translated U a, u≠0) ∧
      energy (signedFunction (translated U a)) (signedFunction (translated U a)) ≤ 8*(U.card:ℝ)^2 := by
  obtain ⟨a,ha,hE⟩ := exists_simultaneous_small_translates hF ({0} : Finset ℕ)
    (fun _ ↦ U) (U.image Neg.neg) (by simpa only [Finset.card_image_of_injective _ neg_injective] using hU)
  refine ⟨a,?_,?_⟩
  · intro u hu hzero
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    apply ha
    exact Finset.mem_image.mpr ⟨x,hx,by linear_combination -hzero⟩
  · rw [translated,energy_signed_translate]
    simpa only [Finset.card_singleton,Nat.cast_one,mul_one] using hE 0 (Finset.mem_singleton_self 0)

lemma nonzero_lift_error (hF : ringChar F≠2) (U : Finset F)
    (hU : ∀ u∈U, u≠0) (hne : U.Nonempty) (E : ℝ)
    (hE : energy (signedFunction U) (signedFunction U) ≤ E) (z : F × F) (hz : z≠0) :
    |(pairCount (parabolaSet U) (parabolaSet U) z:ℝ)-(U.card:ℝ)^2| ≤
      Real.sqrt ((Fintype.card F:ℝ)*E)+3*U.card := by
  have hL := crossCharFiber_l1_sq_le U U Finset.univ (fun _ _ _ _ ↦ Finset.mem_univ _)
  rw [Finset.card_univ] at hL
  have he := hL.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _))
  have hs : (∑ w : F, |(crossCharFiber U U w:ℝ)|) ≤ Real.sqrt ((Fintype.card F:ℝ)*E) :=
    (Real.le_sqrt (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) ((energy_nonneg _ _).trans hE))).mpr he
  have hb := cross_graph_error_allow_opposites hF U U hU hU hne hne z hz
  have hb' : |(pairCount (parabolaSet U) (parabolaSet U) z:ℝ)-(U.card:ℝ)^2| ≤
      (∑ w : F, |(crossCharFiber U U w:ℝ)|)+3*U.card := by
    have hh : |(pairCount (parabolaSet U) (parabolaSet U) z:ℤ)-(U.card:ℤ)^2| ≤
        (∑ w : F, |crossCharFiber U U w|)+3*U.card := by
      convert hb using 1 <;> ring_nf
    exact_mod_cast hh
  linarith

/-- One translation retains an arbitrary parameter set's cyclic flatness and
controls the new graph counts. The two target regimes retain different means. -/
theorem exists_inherited_origin_lift (hF : ringChar F≠2) (U : Finset F)
    (hne : U.Nonempty) (hU : 2*U.card<Fintype.card F) (μ E : ℝ)
    (hflat : ∀ t : F, |(pairCount U U t:ℝ)-μ| ≤ E) :
    ∃ a : F, (∀ u∈translated U a, u≠0) ∧
      (|(pairCount (parabolaSet (translated U a)) (parabolaSet (translated U a)) 0:ℝ)-
        (1+((Fintype.card F:ℝ)-1)*μ)| ≤ ((Fintype.card F:ℝ)-1)*E) ∧
      ∀ z : F × F, z≠0 →
        |(pairCount (parabolaSet (translated U a)) (parabolaSet (translated U a)) z:ℝ)-
          (U.card:ℝ)^2| ≤ Real.sqrt (8*(Fintype.card F:ℝ)*(U.card:ℝ)^2)+3*U.card := by
  obtain ⟨a,ha,hE⟩ := exists_nonzero_low_energy_translate hF U hU
  have hne' : (translated U a).Nonempty := hne.image _
  refine ⟨a,ha,?_,?_⟩
  · apply origin_error_transfer hF _ _ ha ha hne' hne' μ E
    rw [pairCount_translated]
    exact hflat _
  · intro z hz
    have hh := nonzero_lift_error hF (translated U a) ha hne' (8*(U.card:ℝ)^2) hE z hz
    rw [translated_card] at hh
    convert hh using 1 <;> congr 2 <;> ring

end Erdos66InheritedOriginLift
