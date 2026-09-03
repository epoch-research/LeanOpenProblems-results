import Submission.InterceptCollisionCorrectionExplore

/-! Set-level upper bounds survive the intercept construction. The lower
loss is recorded exactly as collision mass, not hidden in the root estimate. -/
namespace Erdos66InterceptUpperAndMass
open Erdos66InterceptCurve Erdos66InterceptCollisionCorrection Erdos66TwofoldFamily
  Erdos66OriginRepair Erdos66CommonOriginFamily Erdos66CyclicVariance Erdos66MixedEnergy
open scoped Classical
set_option maxHeartbeats 1800000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma sum_pairCount_real (A B : Finset (F × F)) :
    (∑z : F × F, (pairCount A B z : ℝ))=(A.card : ℝ)*B.card := by
  simp_rw [← conv_indicators]
  rw [sum_conv,Erdos66CyclicVariance.sum_indicator,Erdos66CyclicVariance.sum_indicator]

def deficit (U : Finset F) (z : F × F) : ℝ :=
  (weightedCount U U z.2 z.1 : ℝ)-pairCount (curveUnion U) (curveUnion U) z

lemma deficit_nonneg (U : Finset F) (hU : ∀u∈U,u≠0) (z : F × F) :
    0≤deficit U z := by
  obtain ⟨t,q⟩ := z
  unfold deficit
  rw [weighted_set_correction U hU]
  have h1 := Nat.cast_nonneg (pairCount (curveUnion U) (collisionSet U) (t,q)) (α := ℝ)
  have h2 := Nat.cast_nonneg (pairCount (collisionSet U) (collisionSet U) (t,q)) (α := ℝ)
  linarith

lemma total_deficit_exact (U : Finset F) (hU : ∀u∈U,u≠0) :
    (∑z : F × F, deficit U z)=2*((curveUnion U).card : ℝ)*(collisionSet U).card+
      ((collisionSet U).card : ℝ)^2 := by
  have he (z : F × F) : deficit U z=
      2*(pairCount (curveUnion U) (collisionSet U) z : ℝ)+
        pairCount (collisionSet U) (collisionSet U) z := by
    obtain ⟨t,q⟩ := z
    unfold deficit
    rw [weighted_set_correction U hU]
    ring
  simp_rw [he,Finset.sum_add_distrib,← Finset.mul_sum,sum_pairCount_real]
  ring

lemma total_deficit_le (hF : ringChar F≠2) (U : Finset F) (hU : ∀u∈U,u≠0) :
    (∑z : F × F, deficit U z)≤2*(Fintype.card F : ℝ)*(U.card : ℝ)^3 := by
  rw [total_deficit_exact U hU]
  have hm := curve_union_mass U hU
  have hc : ((collisionSet U).card : ℝ)≤(U.card : ℝ)^2 := by
    exact_mod_cast collision_card_le_square hF U hU
  have hmul := mul_le_mul_of_nonneg_left hc
    (show 0≤2*(Fintype.card F : ℝ)*(U.card : ℝ) by positivity)
  have he : 2*((curveUnion U).card : ℝ)*(collisionSet U).card+
      ((collisionSet U).card : ℝ)^2=
      2*(Fintype.card F : ℝ)*(U.card : ℝ)*(collisionSet U).card-
        ((collisionSet U).card : ℝ)^2 := by nlinarith only [hm]
  rw [he]
  nlinarith only [hmul,sq_nonneg ((collisionSet U).card : ℝ)]

lemma actual_upper_from_weighted (U : Finset F) (hU : ∀u∈U,u≠0)
    (E : ℝ) (hE : ∀q t, |(weightedCount U U q t : ℝ)-(U.card : ℝ)^2|≤E)
    (z : F × F) : (pairCount (curveUnion U) (curveUnion U) z : ℝ)≤(U.card : ℝ)^2+E := by
  have h1 := abs_le.mp (hE z.2 z.1)
  have h2 := deficit_nonneg U hU z
  unfold deficit at h2
  linarith

lemma actual_upper (hF : ringChar F≠2) (U : Finset F) (hU : ∀u∈U,u≠0)
    (hUU : ∀u∈U,∀v∈U,u+v≠0) (z : F × F) :
    (pairCount (curveUnion U) (curveUnion U) z : ℝ)≤(U.card : ℝ)^2+
      ∑s : F, |(Erdos66CrossGraph.crossCharFiber U U s : ℝ)| := by
  apply actual_upper_from_weighted U hU
  intro q t
  have hh := weightedCount_error hF U U hU hU hUU q t
  have hh' : |weightedCount U U q t-(U.card : ℤ)^2|≤
      ∑s : F, |Erdos66CrossGraph.crossCharFiber U U s| := by
    simpa only [pow_two] using hh
  exact_mod_cast hh'

/-- A small weighted error gives a one-sided pointwise bound and a global
L1 bound for the actual set, but not a pointwise lower bound. -/
theorem total_absolute_error (hF : ringChar F≠2) (U : Finset F)
    (hU : ∀u∈U,u≠0) (E : ℝ)
    (hE : ∀q t, |(weightedCount U U q t : ℝ)-(U.card : ℝ)^2|≤E) :
    (∑z : F × F, |(pairCount (curveUnion U) (curveUnion U) z : ℝ)-(U.card : ℝ)^2|)≤
      (Fintype.card F : ℝ)^2*E+2*(Fintype.card F : ℝ)*(U.card : ℝ)^3 := by
  have hp (z : F × F) :
      |(pairCount (curveUnion U) (curveUnion U) z : ℝ)-(U.card : ℝ)^2|≤E+deficit U z := by
    have ht := abs_sub_le (pairCount (curveUnion U) (curveUnion U) z : ℝ)
      (weightedCount U U z.2 z.1 : ℝ) ((U.card : ℝ)^2)
    have hd : |(pairCount (curveUnion U) (curveUnion U) z : ℝ)-
        (weightedCount U U z.2 z.1 : ℝ)|=deficit U z := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (deficit_nonneg U hU z)
    rw [hd] at ht
    linarith [hE z.2 z.1]
  have hs := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) ↦ hp z)
  have hd := total_deficit_le hF U hU
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    nsmul_eq_mul,Nat.cast_mul] at hs
  nlinarith only [hs,hd]

end Erdos66InterceptUpperAndMass
