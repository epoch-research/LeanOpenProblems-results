import Submission.QuadraticExtensionCharacterExplore

/-! Actual four-coordinate unions for the quadratic lift. Membership on
the old zero slice is preserved, but representation flatness is not. -/
namespace Erdos66QuadraticLiftUnion
open Erdos66QuadraticFieldLift Erdos66QuadraticExtensionCharacter
  Erdos66FiniteField Erdos66OriginRepair Erdos66ParabolaRepair
  Erdos66ShearedParabolaPrefix
open scoped Classical
set_option maxHeartbeats 2500000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (d : F) [Fact (¬IsSquare d)]

noncomputable def liftUnion (U : Finset F) : Finset ((F×F)×(F×F)) :=
  U.biUnion (liftCurve d)

lemma liftUnion_eq_image (U : Finset F) :
    liftUnion d U=(parabolaSet (U.image (algebraMap F (Quad d)))).image (planeEquiv d).symm := by
  ext z
  simp only [liftUnion,liftCurve,parabolaSet_eq_biUnion,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨u,hu,a,ha,haz⟩
    exact ⟨a,⟨algebraMap F (Quad d) u,⟨u,hu,rfl⟩,ha⟩,haz⟩
  · rintro ⟨a,⟨u',⟨u,hu,rfl⟩,ha⟩,haz⟩
    exact ⟨u,hu,a,ha,haz⟩

lemma liftUnion_zero_slice (U : Finset F) (hU : ∀ u∈U, u≠0) (r y : F) :
    ((r,y),((0:F),0))∈liftUnion d U ↔ (r,y)∈parabolaSet U := by
  simp only [liftUnion,parabolaSet_eq_biUnion,Finset.mem_biUnion]
  constructor
  · rintro ⟨u,hu,ha⟩
    exact ⟨u,hu,(liftCurve_zero_slice d u (hU u hu) r y).mp ha⟩
  · rintro ⟨u,hu,ha⟩
    exact ⟨u,hu,(liftCurve_zero_slice d u (hU u hu) r y).mpr ha⟩

lemma liftUnion_pairCount (U V : Finset F) (z : (F×F)×(F×F)) :
    pairCount (liftUnion d U) (liftUnion d V) z=
      pairCount (parabolaSet (U.image (algebraMap F (Quad d))))
        (parabolaSet (V.image (algebraMap F (Quad d)))) (planeEquiv d z) := by
  rw [liftUnion_eq_image,liftUnion_eq_image]
  have he := pairCount_addEquiv (planeEquiv d).symm
    (parabolaSet (U.image (algebraMap F (Quad d))))
    (parabolaSet (V.image (algebraMap F (Quad d)))) (planeEquiv d z)
  simpa only [AddEquiv.symm_apply_apply] using he

lemma nonsquare_im_ne_zero (s : Quad d) (hs : ¬IsSquare s) : s.im≠0 := by
  intro h
  have he : s=algebraMap F (Quad d) s.re := by
    ext <;> simp only [QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,h]
  exact hs (he ▸ base_isSquare d s.re)

/-- The hole lies off the retained old plane. No assumption on the old
parameters' character energy, size, or nonemptiness is needed. -/
theorem liftUnion_has_new_hole (hF : ringChar F≠2) (U V : Finset F) :
    ∃ z : (F×F)×(F×F), z.2≠0 ∧ pairCount (liftUnion d U) (liftUnion d V) z=0 := by
  obtain ⟨s,hs⟩ := FiniteField.exists_nonsquare (F := Quad d) (by rwa [quad_char])
  refine ⟨((0,s.re),(0,s.im)),?_,?_⟩
  · intro he
    exact nonsquare_im_ne_zero d s hs (congrArg Prod.snd he)
  · rw [liftUnion_pairCount]
    have hz : planeEquiv d ((0,s.re),(0,s.im))=(0,s) := by
      apply Prod.ext
      · rfl
      · exact QuadraticAlgebra.mk_eta s
    rw [hz]
    exact mapped_union_nonsquare_hole (algebraMap F (Quad d)) (base_isSquare d) U V s hs

/-- At an OLD target, the inherited zero-slice membership does not imply
inherited counts: the new count is exactly twice the parameter-pair mean. -/
theorem liftUnion_old_target_double (hF : ringChar F≠2) (U V : Finset F)
    (hU : ∀ u∈U, u≠0) (hV : ∀ v∈V, v≠0)
    (hUV : ∀ u∈U, ∀ v∈V, u+v≠0) (hUne : U.Nonempty) (hVne : V.Nonempty) :
    pairCount (liftUnion d U) (liftUnion d V) (((0:F),1),(0,0))=2*U.card*V.card := by
  rw [liftUnion_pairCount]
  have hz : planeEquiv d (((0:F),1),(0,0))=(0,1) := rfl
  rw [hz]
  exact mapped_union_double (algebraMap F (Quad d)) (base_isSquare d)
    (by rwa [quad_char]) U V hU hV hUV hUne hVne

/-- Hence these inherited unions are not uniformly relatively flat about
their nominal parameter-pair mean, even though each individual curve has
joint cap two and retains its old zero slice. -/
theorem not_relative_flat (hF : ringChar F≠2) (U V : Finset F)
    (hUne : U.Nonempty) (hVne : V.Nonempty) (ε : ℝ) (hε : ε<1) :
    ¬∀ z : (F×F)×(F×F),
      |(pairCount (liftUnion d U) (liftUnion d V) z:ℝ)-(U.card:ℝ)*V.card|≤
        ε*((U.card:ℝ)*V.card) := by
  intro h
  obtain ⟨z,hz,hole⟩ := liftUnion_has_new_hole d hF U V
  have hp : (0:ℝ)<(U.card:ℝ)*V.card := mul_pos
    (by exact_mod_cast Finset.card_pos.mpr hUne) (by exact_mod_cast Finset.card_pos.mpr hVne)
  have hh := h z
  rw [hole,Nat.cast_zero,zero_sub,abs_neg,abs_of_pos hp] at hh
  nlinarith only [hh,mul_pos (sub_pos.mpr hε) hp]

end Erdos66QuadraticLiftUnion
