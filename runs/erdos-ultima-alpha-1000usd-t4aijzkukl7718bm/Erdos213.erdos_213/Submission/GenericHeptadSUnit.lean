import Submission.ReciprocalStar

/-! The degree-four pencil found in a finite two-variable S-unit catalog.
These identities give rational distances to two anchors, not an eight-point
configuration or an arbitrary-cardinality construction. No catalog completeness
or finite graph bound is asserted in this file. -/
namespace Erdos213.GenericHeptadSUnit

open ReciprocalStar

lemma quartic_pencil {R : Type*} [CommRing R] (v w : R) :
    v*(w-1)*(v-w-1)^2 - w*(v-1)*(w-v-1)^2 +
      (v-w)*(1-v-w)^2 = 0 := by
  ring

noncomputable def point (v w : ℂ) : ℂ :=
  -(v*(w-1)*(v-w-1)^2)/((v-w)*(1-v-w)^2)

lemma point_complement (v w : ℂ) (hvw : v-w≠0) (hs : 1-v-w≠0) :
    1-point v w = w*(v-1)*(w-v-1)^2/((v-w)*(1-v-w)^2) := by
  have hd : (v-w)*(1-v-w)^2≠0 := mul_ne_zero hvw (pow_ne_zero _ hs)
  unfold point
  apply (eq_div_iff hd).mpr
  field_simp
  linear_combination quartic_pencil v w

/-- Under the eight old norm assumptions, the new point has rational distances
to 0 and 1. This does not assert rational distances to the rest of a heptad. -/
theorem anchor_norms (v w : ℂ) (hvw : v-w≠0) (hs : 1-v-w≠0)
    (hv : RationalNorm v) (hw : RationalNorm w)
    (hv1 : RationalNorm (v-1)) (hw1 : RationalNorm (w-1))
    (hd : RationalNorm (v-w)) (ha : RationalNorm (v-w-1))
    (hb : RationalNorm (w-v-1)) (hc : RationalNorm (1-v-w)) :
    RationalNorm (point v w) ∧ RationalNorm (1-point v w) := by
  have hden := hd.mul (hc.mul hc)
  constructor
  · unfold point
    apply RationalNorm.div ?_ (by simpa only [pow_two] using hden)
    apply (rationalNorm_neg_iff _).mpr
    simpa only [pow_two] using (hv.mul hw1).mul (ha.mul ha)
  · rw [point_complement v w hvw hs]
    apply RationalNorm.div ?_ (by simpa only [pow_two] using hden)
    simpa only [pow_two] using (hw.mul hv1).mul (hb.mul hb)

/-- The six anharmonic transforms preserve the two-anchor norm conditions. -/
lemma anharmonic_norms (z : ℂ) (hz : RationalNorm z) (h1 : RationalNorm (1-z)) :
    RationalNorm z⁻¹ ∧ RationalNorm (1-z⁻¹) ∧
    RationalNorm (1-z)⁻¹ ∧ RationalNorm (1-(1-z)⁻¹) ∧
    RationalNorm (z/(z-1)) ∧ RationalNorm (1-z/(z-1)) := by
  have hone : RationalNorm (1 : ℂ) := ⟨1, by simp⟩
  have hm : RationalNorm (z-1) := rationalNorm_sub_rev h1
  by_cases hz0 : z=0
  · subst z
    simp [RationalNorm]
    exact ⟨1, by norm_num⟩
  by_cases hz1 : z=1
  · subst z
    simp [RationalNorm]
    exact ⟨1, by norm_num⟩
  have hm0 : z-1≠0 := sub_ne_zero.mpr hz1
  have h10 : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hz1)
  refine ⟨by simpa using hone.div hz, ?_, by simpa using hone.div h1, ?_,
    hz.div hm, ?_⟩
  · have he : 1-z⁻¹=(z-1)/z := by field_simp
    rw [he]
    exact hm.div hz
  · have he : 1-(1-z)⁻¹= -z/(1-z) := by field_simp; ring
    rw [he]
    exact ((rationalNorm_neg_iff _).mpr hz).div h1
  · have he : 1-z/(z-1)= -1/(z-1) := by field_simp; ring
    rw [he]
    exact ((rationalNorm_neg_iff _).mpr hone).div hm

#print axioms quartic_pencil
#print axioms anchor_norms
#print axioms anharmonic_norms

end Erdos213.GenericHeptadSUnit
