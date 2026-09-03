import Submission.CrossGraphExplore

/-! The mixed parabola identity with opposite parameters allowed. The
opposite-parameter contribution has a large spike only at the zero target.
This remains a finite-field result. -/
namespace Erdos66DegenerateCrossGraph
open Erdos66FiniteField Erdos66CrossGraph Erdos66OriginRepair
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma opposite_parabola_count (hF : ringChar F ≠ 2) (u t s : F) (hu : u ≠ 0)
    (hz : (t,s) ≠ 0) :
    (Fintype.card {x : F // x^2/u+(t-x)^2/(-u)=s} : ℤ) =
      if t = 0 then 0 else 1 := by
  by_cases ht : t = 0
  · have hs : s ≠ 0 := fun hs ↦ hz (Prod.ext ht hs)
    haveI : IsEmpty {x : F // x^2/u+(t-x)^2/(-u)=s} := by
      refine ⟨fun x ↦ hs ?_⟩
      have he := x.property
      simpa only [ht,zero_sub,neg_sq,div_neg,add_neg_cancel] using he.symm
    simp only [Fintype.card_eq_zero,Nat.cast_zero,if_pos ht]
  · have h2t : 2*t ≠ 0 := mul_ne_zero (Ring.two_ne_zero hF) ht
    have he (x : F) : x^2/u+(t-x)^2/(-u)=s ↔ x=(s*u+t^2)/(2*t) := by
      rw [div_neg,← sub_eq_add_neg,← sub_div,div_eq_iff hu,eq_div_iff h2t]
      constructor <;> intro h <;> linear_combination h
    have hc := Fintype.card_congr (Equiv.subtypeEquivRight he)
    rw [Fintype.card_subtype_eq] at hc
    simp [ht,hc]

lemma opposite_character (u t : F) (hu : u ≠ 0) :
    quadraticChar F u * quadraticChar F (-u) * quadraticChar F (-(t^2)) =
      if t = 0 then 0 else 1 := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht,← map_mul,← map_mul,
      show u*(-u)*(-(t^2)) = (u*t)^2 by ring]
    exact quadraticChar_sq_one' (mul_ne_zero hu ht)

/-- At a nonzero target, an opposite pair contributes one less than the
formal nondegenerate character expression. -/
lemma parabola_sum_count_corrected (hF : ringChar F ≠ 2) (u v t s : F)
    (hu : u ≠ 0) (hv : v ≠ 0) (hz : (t,s) ≠ 0) :
    (Fintype.card {x : F // x^2/u+(t-x)^2/v=s} : ℤ) =
      1 + quadraticChar F u * quadraticChar F v *
        quadraticChar F ((u+v)*s-t^2) - (if u+v=0 then 1 else 0) := by
  by_cases huv : u+v=0
  · have hv' : v = -u := by linear_combination huv
    subst v
    rw [opposite_parabola_count hF u t s hu hz]
    simp only [add_neg_cancel,zero_mul,zero_sub,if_true]
    rw [opposite_character u t hu]
    split_ifs <;> norm_num
  · rw [if_neg huv,sub_zero]
    exact parabola_sum_count hF u v t s hu hv huv

noncomputable def oppositePairs (U V : Finset F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ V, if u+v=0 then 1 else 0

omit [Fintype F] in
lemma oppositePairs_nonneg (U V : Finset F) : 0 ≤ oppositePairs U V := by
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro v hv
  split_ifs <;> norm_num

omit [Fintype F] in
lemma oppositePairs_le_left (U V : Finset F) : oppositePairs U V ≤ U.card := by
  unfold oppositePairs
  calc
    _ ≤ ∑ _u ∈ U, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro u hu
      have he (v : F) : u+v=0 ↔ v = -u := by
        constructor <;> intro h <;> linear_combination h
      simp_rw [he]
      rw [Finset.sum_ite_eq']
      split_ifs <;> norm_num
    _ = _ := by simp

/-- The exact correction to the character identity does not depend on the
nonzero target. -/
lemma crossGraphCount_corrected_identity (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (t s : F) (hz : (t,s) ≠ 0) :
    crossGraphCount U V t s = (U.card : ℤ)*V.card +
      ∑ w : F, crossCharFiber U V w * quadraticChar F (w*s-t^2) - oppositePairs U V := by
  have he : crossGraphCount U V t s = (U.card : ℤ)*V.card +
      (∑ u ∈ U, ∑ v ∈ V, quadraticChar F u * quadraticChar F v *
        quadraticChar F ((u+v)*s-t^2)) - oppositePairs U V := by
    calc
      _ = ∑ u ∈ U, ∑ v ∈ V,
          (1 + quadraticChar F u * quadraticChar F v *
            quadraticChar F ((u+v)*s-t^2) - (if u+v=0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact parabola_sum_count_corrected hF u v t s (hU u hu) (hV v hv) hz
      _ = _ := by
        simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,
          Finset.sum_const,nsmul_eq_mul,mul_one,oppositePairs]
  have hf : (∑ w : F, crossCharFiber U V w * quadraticChar F (w*s-t^2)) =
      ∑ u ∈ U, ∑ v ∈ V, quadraticChar F u * quadraticChar F v *
        quadraticChar F ((u+v)*s-t^2) := by
    simp only [crossCharFiber,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rwa [hf]

lemma crossGraphCount_corrected_error (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (t s : F) (hz : (t,s) ≠ 0) :
    |crossGraphCount U V t s-(U.card : ℤ)*V.card| ≤
      (∑ w : F, |crossCharFiber U V w|)+U.card := by
  rw [crossGraphCount_corrected_identity hF U V hU hV t s hz]
  have hs : |∑ w : F, crossCharFiber U V w * quadraticChar F (w*s-t^2)| ≤
      ∑ w : F, |crossCharFiber U V w| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro w hw
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (quadraticChar_abs_le_one (w*s-t^2)) (abs_nonneg _)
  have hp := oppositePairs_le_left U V
  have hn := oppositePairs_nonneg U V
  have ha := abs_sub (∑ w : F, crossCharFiber U V w * quadraticChar F (w*s-t^2))
    (oppositePairs U V)
  rw [abs_of_nonneg hn] at ha
  convert ha.trans (add_le_add hs hp) using 1
  congr 1
  ring

/-- Unlike `cross_graph_error`, this estimate permits opposite parameters.
The diagonal spike is excluded explicitly by `hz`. -/
theorem cross_graph_error_allow_opposites (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (hUne : U.Nonempty) (hVne : V.Nonempty) (z : F × F) (hz : z ≠ 0) :
    |(pairCount (parabolaSet U) (parabolaSet V) z : ℤ)-(U.card : ℤ)*V.card| ≤
      (∑ w : F, |crossCharFiber U V w|)+2*U.card+V.card := by
  obtain ⟨t,s⟩ := z
  rw [parabolaSet_crossCount_eq]
  have hu : 0 ≤ (U.card : ℤ)-1 := by
    have hh := Finset.card_pos.mpr hUne
    omega
  have hv : 0 ≤ (V.card : ℤ)-1 := by
    have hh := Finset.card_pos.mpr hVne
    omega
  obtain ⟨hiU0,hiU1⟩ := graphIndicator_bounds U (t,s)
  obtain ⟨hiV0,hiV1⟩ := graphIndicator_bounds V (t,s)
  have he := crossGraphCount_correction U V hU hV hUne hVne t s
  rw [if_neg hz,mul_zero,add_zero] at he
  have hb := crossGraphCount_corrected_error hF U V hU hV t s hz
  rw [abs_le] at hb ⊢
  constructor <;> nlinarith [mul_nonneg hu hiV0,mul_nonneg hv hiU0,
    mul_nonneg hu (sub_nonneg.mpr hiV1),mul_nonneg hv (sub_nonneg.mpr hiU1)]

end Erdos66DegenerateCrossGraph
