import Submission.PrefixFaithfulParabolaLiftExplore

/-! The finite faithful-lift error can be charged to the size of a parameter
sum support, rather than the size of the ambient field. This estimate does
not bound spatially clipped or row-dependent pair counts. -/
namespace Erdos66SupportSensitiveFaithfulLift
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph Erdos66DegenerateCrossGraph
  Erdos66InheritedOriginLift Erdos66TranslatedMixedFiber Erdos66MixedEnergy
  Erdos66PrefixFaithfulParabolaLift Erdos66ShearedParabolaPrefix
open scoped Classical
set_option maxHeartbeats 1500000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma nonzero_lift_error_with_support (hF : ringChar F≠2) (U S : Finset F)
    (hU : ∀ u∈U, u≠0) (hne : U.Nonempty)
    (hS : ∀ u∈U, ∀ v∈U, u+v∈S) (E : ℝ)
    (hE : energy (signedFunction U) (signedFunction U) ≤ E)
    (z : F × F) (hz : z≠0) :
    |(pairCount (parabolaSet U) (parabolaSet U) z:ℝ)-(U.card:ℝ)^2| ≤
      Real.sqrt ((S.card:ℝ)*E)+3*U.card := by
  have hL := crossCharFiber_l1_sq_le U U S hS
  have he := hL.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _))
  have hs : (∑ w : F, |(crossCharFiber U U w:ℝ)|) ≤ Real.sqrt ((S.card:ℝ)*E) :=
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

/-- An arbitrary parameter set with a small sum support admits a complete
finite lift with the corresponding improved error and exact first row.
The exceptional target is still excluded explicitly. -/
theorem exists_support_sensitive_faithful_lift (hF : ringChar F≠2)
    (U S : Finset F) (hne : U.Nonempty) (hU : 2*U.card<Fintype.card F)
    (hS : ∀ u∈U, ∀ v∈U, u+v∈S) :
    ∃ a : F, (∀ u∈translated U a, u≠0) ∧
      (∀ x : F, (x,0)∈faithfulLift U a ↔ x∈U) ∧
      ∀ z : F × F, shear.symm (z-(-a,0)-(-a,0))≠0 →
        |(pairCount (faithfulLift U a) (faithfulLift U a) z:ℝ)-(U.card:ℝ)^2| ≤
          Real.sqrt (8*(S.card:ℝ)*(U.card:ℝ)^2)+3*U.card+2 := by
  obtain ⟨a,ha,hE⟩ := exists_nonzero_low_energy_translate hF U hU
  let T := S.image (fun w ↦ a+a+w)
  have hT : T.card=S.card := Finset.card_image_of_injective _ (add_right_injective _)
  have hs : ∀u∈translated U a, ∀v∈translated U a, u+v∈T := by
    intro u hu v hv
    change u∈U.image (fun x ↦ a+x) at hu
    change v∈U.image (fun x ↦ a+x) at hv
    obtain ⟨u0,hu0,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v0,hv0,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨u0+v0,hS u0 hu0 v0 hv0,by ring⟩
  refine ⟨a,ha,faithfulLift_row U hne a ha,fun z hz ↦ ?_⟩
  have he := nonzero_lift_error_with_support hF (translated U a) T ha (hne.image _) hs
    (8*(U.card:ℝ)^2) hE _ hz
  rw [hT,translated_card] at he
  have hc := faithfulLift_count_comparison U a z
  have ht := abs_sub_le (pairCount (faithfulLift U a) (faithfulLift U a) z:ℝ)
    (pairCount (parabolaSet (translated U a)) (parabolaSet (translated U a))
      (shear.symm (z-(-a,0)-(-a,0))):ℝ) ((U.card:ℝ)^2)
  have hr : (S.card:ℝ)*(8*(U.card:ℝ)^2)=8*(S.card:ℝ)*(U.card:ℝ)^2 := by ring
  rw [hr] at he
  linarith

end Erdos66SupportSensitiveFaithfulLift
