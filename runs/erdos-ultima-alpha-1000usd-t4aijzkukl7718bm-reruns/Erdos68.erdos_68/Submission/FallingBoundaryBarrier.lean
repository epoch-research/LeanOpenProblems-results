import Submission.FallingResidueForms

/-!
An obstruction for clearing the separate column boundaries of the explicit
falling-residue family. This does not assert an obstruction for the reduced
denominator of their aggregate, and does not settle Erdős 68.
-/
namespace FallingBoundaryBarrier
open FallingResidueForms Erdos68Development TailPowerExpansion

lemma elementary_clearing_bound (x y m : ℤ) (hx : 1 < x) (hy : x < y)
    (hm : 0 < m) (hd : x*y-2*x+1 ∣ m*(y-1)) : x < m := by
  have hpos : 0 < m*(x-1) := mul_pos hm (by omega)
  have hd' : x*y-2*x+1 ∣ m*(x-1) := by
    have hh := dvd_sub (dvd_mul_of_dvd_right hd x)
      (dvd_mul_left (x*y-2*x+1) m)
    convert hh using 1
    ring
  have hl := Int.le_of_dvd hpos hd'
  have hgap : x*(x-1) < x*y-2*x+1 := by
    have ht : 0 ≤ x*(y-x-1) := mul_nonneg (by omega) (by omega)
    nlinarith
  by_contra hn
  have hh : m*(x-1) ≤ x*(x-1) :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  omega

lemma power_gap (r : ℕ) : (2:ℤ)^(r+1) < (3:ℤ)^(r+1) :=
  pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)

lemma two_power_gt_one (r : ℕ) : (1:ℤ) < 2^(r+1) := by
  simpa using (pow_lt_pow_left₀ (by norm_num : (1:ℤ)<2)
    (by norm_num) (show r+1 ≠ 0 by omega))

lemma leading_eq (r : ℕ) :
    leading r = (2:ℤ)^(r+1)*(3:ℤ)^(r+1)-2*2^(r+1)+1 := by
  unfold leading
  rw [← mul_pow]
  norm_num

lemma leading_pos (r : ℕ) : 0 < leading r := by
  rw [leading_eq]
  have hx := two_power_gt_one r
  have hy := power_gap r
  have ht : 0 ≤ (2:ℤ)^(r+1)*((3:ℤ)^(r+1)-2) :=
    mul_nonneg (by positivity) (by omega)
  nlinarith

/-- Even clearing just the last individual rational boundary forces a
multiplier strictly larger than the power of two controlling the omitted
columns. This hypothesis is not automatic for the aggregate boundary. -/
theorem separate_clearing_large (r : ℕ) (m : ℤ) (hm : 0 < m)
    (hd : leading r ∣ m*boundary r) : (2:ℤ)^(r+1) < m := by
  apply elementary_clearing_bound _ _ _ (two_power_gt_one r) (power_gap r) hm
  simpa only [leading_eq, boundary] using hd

/-- The individual boundary's reduced denominator still exceeds 2^(r+1). -/
theorem individual_reduced_den_large (r : ℕ) :
    2^(r+1) < ((boundary r : ℚ)/(leading r : ℚ)).den := by
  let q : ℚ := (boundary r : ℚ)/(leading r : ℚ)
  have hd0 : (leading r : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (leading_pos r)
  have hq := Rat.den_mul_eq_num q
  change (q.den : ℚ)*((boundary r : ℚ)/(leading r : ℚ)) = q.num at hq
  have hid : (q.den : ℤ)*boundary r = q.num*leading r := by
    apply Rat.intCast_injective
    push_cast
    exact (div_eq_iff hd0).mp (by simpa only [mul_div_assoc] using hq)
  have hd : leading r ∣ (q.den : ℤ)*boundary r := by
    rw [hid]
    exact dvd_mul_left _ _
  have h := separate_clearing_large r (q.den : ℤ) (by exact_mod_cast q.pos) hd
  change 2^(r+1) < q.den
  exact_mod_cast h

noncomputable def approximation (r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (r+1), (boundary j : ℚ)/(leading j : ℚ)

lemma normalized_boundary_lt (j : ℕ) :
    (boundary j : ℝ)/(leading j : ℝ) < ∑' k : ℕ, powerTerm j k := by
  apply (div_lt_iff₀ (show (0:ℝ) < leading j by exact_mod_cast leading_pos j)).mpr
  nlinarith [column_form_pos j]

lemma approximation_error_lower (r : ℕ) :
    1/(2:ℝ)^(r+1) < (∑' k : ℕ, term k) - (approximation r : ℝ) := by
  have he := finite_tail_expansion (r+1) 0
  have ht := rowError_lt_tailError (r+1) 0
  simp only [Nat.add_zero, columnTail] at he
  have hs : (approximation r : ℝ) ≤
      ∑ j ∈ Finset.range (r+1), ∑' k : ℕ, powerTerm j k := by
    simp only [approximation, Rat.cast_sum, Rat.cast_div, Rat.cast_intCast]
    exact Finset.sum_le_sum (fun j _ => (normalized_boundary_lt j).le)
  have hrow : rowError (r+1) 0 = 1/(2:ℝ)^(r+1) := by norm_num [rowError]
  rw [hrow] at ht
  linarith

/-- A genuine infinite barrier for separate boundary clearing, not a
statement about arbitrary or reduced aggregate denominators. -/
theorem separately_cleared_error_gt_one (r : ℕ) (m : ℤ) (hm : 0 < m)
    (hd : leading r ∣ m*boundary r) :
    1 < (m : ℝ)*((∑' k : ℕ, term k) - (approximation r : ℝ)) := by
  have hpow : (0:ℝ) < 2^(r+1) := by positivity
  have he := approximation_error_lower r
  have hm' : (2:ℝ)^(r+1) < m := by
    exact_mod_cast separate_clearing_large r m hm hd
  have he0 : 0 < (∑' k : ℕ, term k) - (approximation r : ℝ) :=
    (one_div_pos.mpr hpow).trans he
  have h1 : 1 < (2:ℝ)^(r+1)*((∑' k : ℕ, term k) - (approximation r : ℝ)) := by
    have hh := (div_lt_iff₀ hpow).mp he
    nlinarith
  exact h1.trans (mul_lt_mul_of_pos_right hm' he0)

end FallingBoundaryBarrier

#print axioms FallingBoundaryBarrier.separate_clearing_large
#print axioms FallingBoundaryBarrier.approximation_error_lower
#print axioms FallingBoundaryBarrier.separately_cleared_error_gt_one

#print axioms FallingBoundaryBarrier.individual_reduced_den_large
