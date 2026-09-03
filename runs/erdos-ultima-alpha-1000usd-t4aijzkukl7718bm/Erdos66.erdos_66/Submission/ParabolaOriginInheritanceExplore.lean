import Submission.DegenerateCrossGraphExplore

/-! The exact origin count when opposite parabola parameters are allowed.
This is a finite-field identity, not an infinite natural-number construction. -/
namespace Erdos66ParabolaOriginInheritance
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph Erdos66DegenerateCrossGraph
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
set_option maxHeartbeats 1300000

omit [Fintype F] in
lemma oppositePairs_eq_pairCount (U V : Finset F) :
    oppositePairs U V=(pairCount U V 0:ℤ) := by
  unfold oppositePairs pairCount
  have he (u v : F) : u+v=0 ↔ v=-u := by constructor <;> intro h <;> linear_combination h
  simp_rw [he]
  simp only [Finset.sum_ite_eq',zero_sub,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]

lemma parabola_root_origin (hF : ringChar F ≠ 2) (u v : F) (hu : u≠0) (hv : v≠0) :
    (Fintype.card {x : F // x^2/u+(0-x)^2/v=0}:ℤ)=
      1+((Fintype.card F:ℤ)-1)*(if u+v=0 then 1 else 0) := by
  by_cases huv : u+v=0
  · have hv' : v=-u := by linear_combination huv
    have he (x : F) : x^2/u+(0-x)^2/v=0 := by simp [hv',div_neg]
    have hall : (fun x : F ↦ x^2/u+(0-x)^2/v=0)=(fun _ ↦ True) := by
      funext x
      exact propext ⟨fun _ ↦ trivial,fun _ ↦ he x⟩
    simp only [hall,Fintype.card_subtype_true,if_pos huv,mul_one]
    ring
  · rw [parabola_sum_count hF u v 0 0 hu hv huv]
    simp [huv]

lemma crossGraphCount_origin (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u∈U, u≠0) (hV : ∀ v∈V, v≠0) :
    crossGraphCount U V 0 0=(U.card:ℤ)*V.card+
      ((Fintype.card F:ℤ)-1)*(pairCount U V 0:ℤ) := by
  calc
    _ = ∑ u∈U, ∑ v∈V, (1+((Fintype.card F:ℤ)-1)*(if u+v=0 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      exact parabola_root_origin hF u v (hU u hu) (hV v hv)
    _ = _ := by
      rw [←oppositePairs_eq_pairCount]
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,
        ←Finset.mul_sum,oppositePairs]

/-- Opposite parameters inherit the old representation count at the origin.
They need not be forbidden or corrected by an external origin packet. -/
theorem parabola_origin (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u∈U, u≠0) (hV : ∀ v∈V, v≠0)
    (hUne : U.Nonempty) (hVne : V.Nonempty) :
    (pairCount (parabolaSet U) (parabolaSet V) 0:ℤ)=
      1+((Fintype.card F:ℤ)-1)*(pairCount U V 0:ℤ) := by
  have hu0 : graphIndicator U (0,0)=1 := by
    obtain ⟨u,hu⟩ := hUne
    simp [graphIndicator,show ∃ u, u∈U from ⟨u,hu⟩]
  have hv0 : graphIndicator V (0,0)=1 := by
    obtain ⟨v,hv⟩ := hVne
    simp [graphIndicator,show ∃ v, v∈V from ⟨v,hv⟩]
  have he := crossGraphCount_correction U V hU hV hUne hVne 0 0
  rw [crossGraphCount_origin hF U V hU hV,hu0,hv0] at he
  norm_num at he
  rw [parabolaSet_crossCount_eq]
  change finiteConv (graphIndicator U) (graphIndicator V) (0,0)=_
  nlinarith only [he]

/-- Accurate parameter counts at zero give accurate lifted counts there, with
an explicit bounded correction and the field-size amplification retained. -/
lemma origin_error_transfer (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u∈U, u≠0) (hV : ∀ v∈V, v≠0)
    (hUne : U.Nonempty) (hVne : V.Nonempty) (μ E : ℝ)
    (h : |(pairCount U V 0:ℝ)-μ| ≤ E) :
    |(pairCount (parabolaSet U) (parabolaSet V) 0:ℝ)-
      (1+((Fintype.card F:ℝ)-1)*μ)| ≤ ((Fintype.card F:ℝ)-1)*E := by
  have he : (pairCount (parabolaSet U) (parabolaSet V) 0:ℝ)=
      1+((Fintype.card F:ℝ)-1)*(pairCount U V 0:ℝ) := by
    exact_mod_cast parabola_origin hF U V hU hV hUne hVne
  have hc : 0 ≤ (Fintype.card F:ℝ)-1 := by
    have hn := Fintype.card_pos (α := F)
    exact_mod_cast (show (0:ℤ) ≤ (Fintype.card F:ℤ)-1 by omega)
  rw [he,show 1+((Fintype.card F:ℝ)-1)*(pairCount U V 0:ℝ)-
      (1+((Fintype.card F:ℝ)-1)*μ)=((Fintype.card F:ℝ)-1)*((pairCount U V 0:ℝ)-μ) by ring,
    abs_mul,abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left h hc

end Erdos66ParabolaOriginInheritance
