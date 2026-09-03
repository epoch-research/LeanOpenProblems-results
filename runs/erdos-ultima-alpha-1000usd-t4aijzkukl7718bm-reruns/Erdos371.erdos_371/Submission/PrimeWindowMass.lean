import FormalConjecturesUtil
import Submission.PrimeLogMass

/-! Finite prime-window consequences of Mertens' first estimate. -/

namespace Erdos371PrimeWindowMass

open Finset Filter Erdos371PrimeLogMass
open scoped Topology

noncomputable def window (L U : ℕ) : Finset ℕ :=
  (U+1).primesBelow \ (L+1).primesBelow

noncomputable def reciprocal (L U : ℕ) : ℝ :=
  ∑ p ∈ window L U, 1/(p:ℝ)

lemma mem_window {L U p : ℕ} : p ∈ window L U ↔ p.Prime ∧ L < p ∧ p ≤ U := by
  classical
  unfold window
  rw [Finset.mem_sdiff]
  simp only [Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hu,hp⟩,hL⟩
    refine ⟨hp,?_,by omega⟩
    by_contra h
    exact hL ⟨by omega,hp⟩
  · rintro ⟨hp,hL,hU⟩
    refine ⟨⟨by omega,hp⟩,?_⟩
    rintro ⟨h,_⟩
    omega

lemma window_weighted_sum {L U : ℕ} (hLU : L ≤ U) :
    (∑ p ∈ window L U, Real.log (p:ℝ)/(p:ℝ)) = mass U-mass L := by
  unfold window mass
  apply sum_sdiff_eq_sub
  intro p hp
  obtain ⟨hpL, hp⟩ := Nat.mem_primesBelow.mp hp
  exact Nat.mem_primesBelow.mpr ⟨by omega,hp⟩

lemma weighted_window_le (L U : ℕ) :
    (∑ p ∈ window L U, Real.log (p:ℝ)/(p:ℝ)) ≤ Real.log U*reciprocal L U := by
  unfold reciprocal
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hprime,_,hpU⟩ := mem_window.mp hp
  have hh := Real.log_le_log (Nat.cast_pos.mpr hprime.pos) (Nat.cast_le.mpr hpU)
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg p)

noncomputable def errorConstant : ℝ := 1+correctionBound+Real.log 4

lemma errorConstant_nonneg : 0 ≤ errorConstant := by
  unfold errorConstant
  have hh := correctionBound_nonneg
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

/-- A finite lower bound, with error independent of both endpoints. -/
lemma log_difference_le_reciprocal {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) :
    Real.log U-Real.log L-errorConstant ≤ Real.log U*reciprocal L U := by
  have hh := weighted_window_le L U
  rw [window_weighted_sum hLU] at hh
  have hlow := (mass_bounds (show 0 < U by omega)).1
  have hupp := (mass_bounds hL).2
  unfold errorConstant
  linarith

lemma adjacent_power_window {t a : ℕ} (ht : 1 < t) :
    Real.log t-errorConstant ≤ ((a+1:ℕ):ℝ)*Real.log t*reciprocal (t^a) (t^(a+1)) := by
  have hh := log_difference_le_reciprocal (pow_pos (by omega : 0<t) a)
    (Nat.pow_le_pow_right (by omega : 0<t) (by omega : a≤a+1))
  push_cast at hh
  simp only [Real.log_pow] at hh
  push_cast at hh ⊢
  nlinarith

lemma reciprocal_nonneg (L U : ℕ) : 0 ≤ reciprocal L U := by
  unfold reciprocal
  positivity

lemma reciprocal_add {L M U : ℕ} (hLM : L ≤ M) (hMU : M ≤ U) :
    reciprocal L M + reciprocal M U = reciprocal L U := by
  have hd : Disjoint (window L M) (window M U) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hh := mem_window.mp hp
    have hh' := mem_window.mp hq
    omega
  have he : window L M ∪ window M U = window L U := by
    ext p
    simp only [mem_union, mem_window]
    constructor
    · rintro (⟨hp,hpL,hpM⟩ | ⟨hp,hpM,hpU⟩)
      · exact ⟨hp,hpL,hpM.trans hMU⟩
      · exact ⟨hp,hLM.trans_lt hpM,hpU⟩
    · rintro ⟨hp,hpL,hpU⟩
      by_cases h : p ≤ M
      · exact Or.inl ⟨hp,hpL,h⟩
      · exact Or.inr ⟨hp,by omega,hpU⟩
  unfold reciprocal
  rw [← sum_union hd, he]

/-- Three windows already give more than one half of a unit of reciprocal
prime mass between `t^4` and `t^7`, up to a vanishing error. -/
theorem fourth_to_seventh_window {t : ℕ} (ht : 1 < t) :
    107/210 - 3*errorConstant/Real.log t ≤ reciprocal (t^4) (t^7) := by
  have h4 := adjacent_power_window (t := t) (a := 4) ht
  have h5 := adjacent_power_window (t := t) (a := 5) ht
  have h6 := adjacent_power_window (t := t) (a := 6) ht
  norm_num at h4 h5 h6
  have ht0 : 0 < t := by omega
  have h45 : t^4 ≤ t^5 := Nat.pow_le_pow_right ht0 (by omega)
  have h56 : t^5 ≤ t^6 := Nat.pow_le_pow_right ht0 (by omega)
  have h67 : t^6 ≤ t^7 := Nat.pow_le_pow_right ht0 (by omega)
  have he : reciprocal (t^4) (t^7) = reciprocal (t^4) (t^5)+
      reciprocal (t^5) (t^6)+reciprocal (t^6) (t^7) := by
    rw [← reciprocal_add h45 (h56.trans h67), ← reciprocal_add h56 h67]
    ring
  have hl : 0 < Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast ht)
  apply (mul_le_mul_iff_left₀ hl).mp
  have hE := errorConstant_nonneg
  rw [sub_mul, div_mul_cancel₀ _ hl.ne']
  rw [he]
  nlinarith

lemma eventually_window_gt_half : ∀ᶠ t : ℕ in atTop,
    101/200 ≤ reciprocal (t^4) (t^7) := by
  have hlog : Tendsto (fun t : ℕ => Real.log (t:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr := (hlog.const_div_atTop (3*errorConstant)).eventually_lt_const
    (show (0:ℝ)<107/210-101/200 by norm_num)
  filter_upwards [herr, eventually_gt_atTop 1] with t ht ht1
  have hh := fourth_to_seventh_window ht1
  linarith

end Erdos371PrimeWindowMass

#print axioms Erdos371PrimeWindowMass.fourth_to_seventh_window
#print axioms Erdos371PrimeWindowMass.eventually_window_gt_half
