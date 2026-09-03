import Submission.NewmanRootBounds

/-! Argument-sensitive necessary conditions on Newman roots. These do not
bound the degree or settle the pure-power evaluation problem. -/
namespace Erdos406Newman

lemma lower_angular_root_bound (z : ℂ) (w : List ℕ)
    (hw : w ⊆ [0,1]) (hz : Nat.ofDigits z (1 :: w) = 0)
    (hr1 : ‖z‖ < 1) :
    1 - ‖z‖ < (2*‖z‖-1) * ‖1-z‖ := by
  have hn : z ≠ 0 := by
    intro he
    simp [he, Nat.ofDigits] at hz
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hn
  let v := 1 :: w
  let a := Nat.ofDigits ‖z‖ v
  let b := Nat.ofDigits ‖z‖ (complement v)
  have hv : v ⊆ [0,1] := List.cons_subset.mpr ⟨by simp,hw⟩
  have ha : 2 ≤ a := by
    have he : z * Nat.ofDigits z w = -1 := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa [Nat.ofDigits, add_comm] using hz
    have hh := mul_le_mul_of_nonneg_left (norm_ofDigits_le z w) (norm_nonneg z)
    rw [← norm_mul, he] at hh
    norm_num at hh
    dsimp [a, v, Nat.ofDigits]
    norm_num only [Nat.cast_one]
    linarith
  have hb : 0 ≤ b := ofDigits_nonneg _ (norm_nonneg z) _
  have hg : (a+b)*(1-‖z‖) = 1-‖z‖^v.length := by
    simpa only [mul_comm] using partition_geom ‖z‖ v hv
  have hgC : (1-z)*Nat.ofDigits z (complement v) = 1-z^v.length := by
    have hh := partition_geom z v hv
    change Nat.ofDigits z v = 0 at hz
    simpa only [hz, zero_add] using hh
  have hN : 1-‖z‖^v.length ≤ ‖1-z‖*b := by
    calc
      1-‖z‖^v.length ≤ ‖1-z^v.length‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) (z^v.length)
      _ = ‖1-z‖ * ‖Nat.ofDigits z (complement v)‖ := by rw [← hgC, norm_mul]
      _ ≤ ‖1-z‖*b := mul_le_mul_of_nonneg_left
        (norm_ofDigits_le z (complement v)) (norm_nonneg _)
  have hd : 0 < 1-‖z‖ := by linarith
  have hlin : a*(1-‖z‖) ≤ b*(‖1-z‖+‖z‖-1) := by nlinarith only [hg,hN]
  have hpos : 0 < ‖1-z‖+‖z‖-1 := by
    by_contra h
    have hh := mul_nonpos_of_nonneg_of_nonpos hb (le_of_not_gt h)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hN hd.le
  have hgeom := congrArg (fun x : ℝ => ‖1-z‖*x) hg
  have hlow := mul_le_mul_of_nonneg_right ha
    (mul_nonneg (norm_nonneg (1-z)) hd.le)
  have hbound : 2*‖1-z‖*(1-‖z‖) ≤
      (‖1-z‖+‖z‖-1)*(1-‖z‖^v.length) := by
    nlinarith only [hmul,hgeom,hlow]
  have hp : 0 < (‖1-z‖+‖z‖-1)*‖z‖^v.length :=
    mul_pos hpos (pow_pos hr0 _)
  nlinarith only [hbound,hp]

lemma upper_angular_root_bound (z : ℂ) (w : List ℕ)
    (hw : w ⊆ [0,1]) (hz : Nat.ofDigits z (w ++ [1]) = 0)
    (hr : 1 < ‖z‖) :
    ‖z‖*(‖z‖-1) < (2-‖z‖)*‖z-1‖ := by
  have hn : z ≠ 0 := by intro h; norm_num [h] at hr
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hn
  have hrev : Nat.ofDigits z⁻¹ ((w ++ [1]).reverse) = 0 := by
    have hh := ofDigits_reverse_reciprocal z hn (w ++ [1])
    rw [hz, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hn)
  have hw' : w.reverse ⊆ [0,1] := fun a ha => hw (List.mem_reverse.mp ha)
  have hi : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hr
  have hb := lower_angular_root_bound z⁻¹ w.reverse hw' (by simpa using hrev) hi
  have hnrm : ‖1-z⁻¹‖*‖z‖ = ‖z-1‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
  rw [norm_inv] at hb
  have hh := mul_lt_mul_of_pos_right hb (pow_pos hr0 2)
  have he1 : (1-‖z‖⁻¹)*‖z‖^2 = ‖z‖*(‖z‖-1) := by field_simp
  have he2 : ((2*‖z‖⁻¹-1)*‖1-z⁻¹‖)*‖z‖^2 =
      (2-‖z‖)*(‖1-z⁻¹‖*‖z‖) := by field_simp
  rw [he1,he2,hnrm] at hh
  exact hh

#print axioms lower_angular_root_bound
#print axioms upper_angular_root_bound
end Erdos406Newman
