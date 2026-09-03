import Submission.Development

/-!
Rectangular truncations of the geometric expansion cannot produce a small
integer linear form, even after their rational values are reduced. This is
an auxiliary obstruction, not a solution to Erdős 68.
-/

namespace Erdos68Development

def rectangleNumerator : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, r => (n + 2) ^ (r + 1) * rectangleNumerator n r +
      ∑ j ∈ Finset.range (r + 1), (n + 2).factorial ^ j

def rectangleApprox (n r : ℕ) : ℚ :=
  (rectangleNumerator n r : ℚ) / ((n + 1).factorial : ℚ) ^ (r + 1)

lemma scaled_geometric_sum (a : ℚ) (ha : a ≠ 0) (r : ℕ) :
    a ^ (r + 1) * (∑ j ∈ Finset.range (r + 1), 1 / a ^ (j + 1)) =
      ∑ j ∈ Finset.range (r + 1), a ^ j := by
  induction r with
  | zero => simp [ha]
  | succ r ih =>
    have hg : (∑ j ∈ Finset.range (r + 2), a ^ j) =
        1 + a * (∑ j ∈ Finset.range (r + 1), a ^ j) := by
      rw [show r + 2 = (r + 1) + 1 by omega, Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', ← Finset.mul_sum]
      ring
    rw [show r + 1 + 1 = r + 2 by omega, hg,
      show r + 2 = (r + 1) + 1 by omega, Finset.sum_range_succ, mul_add,
      mul_one_div_cancel (pow_ne_zero _ ha)]
    rw [pow_succ]
    calc
      a ^ (r + 1) * a * (∑ j ∈ Finset.range (r + 1), 1 / a ^ (j + 1)) + 1 =
          a * (a ^ (r + 1) * (∑ j ∈ Finset.range (r + 1), 1 / a ^ (j + 1))) + 1 := by ring
      _ = _ := by rw [ih]; ring

lemma rectangleApprox_eq_sum (n r : ℕ) :
    rectangleApprox n r = ∑ k ∈ Finset.range n,
      ∑ j ∈ Finset.range (r + 1), 1 / ((k + 2).factorial : ℚ) ^ (j + 1) := by
  induction n with
  | zero => simp [rectangleApprox, rectangleNumerator]
  | succ n ih =>
    have hf : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    have hn : (n + 2 : ℚ) ≠ 0 := by positivity
    have hfac : ((n + 2).factorial : ℚ) = (n + 2) * (n + 1).factorial := by
      rw [Nat.factorial_succ (n + 1)]
      push_cast
      ring
    have hg := scaled_geometric_sum ((n + 2).factorial : ℚ) (by positivity) r
    rw [Finset.sum_range_succ, ← ih]
    simp only [rectangleApprox, rectangleNumerator, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_sum]
    rw [show n + 1 + 1 = n + 2 by omega]
    rw [← hg, hfac, mul_pow]
    field_simp
    ring

lemma rectangleNumerator_coprime (n r : ℕ) :
    (n + 2).Coprime (rectangleNumerator (n + 1) r) := by
  have hfac : (n + 2).factorial % (n + 2) = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_factorial (by omega) le_rfl)
  have hmod : rectangleNumerator (n + 1) r % (n + 2) = 1 := by
    simp only [rectangleNumerator, Finset.sum_range_succ', pow_zero, pow_succ, ← Finset.sum_mul]
    simp [Nat.add_mod, Nat.mul_mod, hfac, Nat.mod_eq_of_lt (by omega : 1 < n + 2)]
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec, hmod]
  simp

lemma rectangle_den_dvd (n r : ℕ) :
    (n + 2) ^ (r + 1) ∣ (rectangleApprox (n + 1) r).den := by
  let q := rectangleApprox (n + 1) r
  have hq : (q.den : ℚ) * q = q.num := Rat.den_mul_eq_num q
  change (q.den : ℚ) *
    ((rectangleNumerator (n + 1) r : ℚ) / ((n + 2).factorial : ℚ) ^ (r + 1)) = q.num at hq
  have hf : (((n + 2).factorial : ℚ) ^ (r + 1)) ≠ 0 := by positivity
  have hid : (q.den : ℤ) * (rectangleNumerator (n + 1) r : ℤ) =
      q.num * ((n + 2).factorial : ℤ) ^ (r + 1) := by
    apply Rat.intCast_injective
    push_cast
    exact (div_eq_iff hf).mp (by simpa only [mul_div_assoc] using hq)
  have hd : ((n + 2 : ℤ) ^ (r + 1)) ∣ ((n + 2).factorial : ℤ) ^ (r + 1) := by
    apply pow_dvd_pow_of_dvd
    exact_mod_cast Nat.dvd_factorial (by omega : 0 < n + 2) (le_refl (n + 2))
  have hprod : ((n + 2 : ℤ) ^ (r + 1)) ∣
      (rectangleNumerator (n + 1) r : ℤ) * q.den := by
    rw [mul_comm, hid]
    exact dvd_mul_of_dvd_right hd _
  have hc : IsCoprime ((n + 2 : ℤ) ^ (r + 1)) (rectangleNumerator (n + 1) r : ℤ) := by
    exact_mod_cast ((rectangleNumerator_coprime n r).pow_left (r + 1)).isCoprime
  exact_mod_cast hc.dvd_of_dvd_mul_left hprod

lemma cast_rectangleApprox (n r : ℕ) :
    (rectangleApprox n r : ℝ) =
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (r + 1), powerTerm j k := by
  rw [rectangleApprox_eq_sum]
  simp [powerTerm]

lemma row_partial_le (k r : ℕ) :
    (∑ j ∈ Finset.range (r + 1), powerTerm j k) ≤ term k := by
  rw [← sum_powerTerm_orders k]
  exact (summable_powerTerm_orders k).sum_le_tsum _ (fun j _ => (powerTerm_pos j k).le)

lemma first_row_remainder (r : ℕ) :
    term 0 - ∑ j ∈ Finset.range (r + 1), powerTerm j 0 = 1 / (2 : ℝ) ^ (r + 1) := by
  have hq := scaled_geometric_sum 2 (by norm_num) r
  have hg := geom_sum_mul (2 : ℚ) (r + 1)
  norm_num at hg
  rw [hg] at hq
  have h : (2 : ℝ) ^ (r + 1) * (∑ j ∈ Finset.range (r + 1), 1 / (2 : ℝ) ^ (j + 1)) =
      (2 : ℝ) ^ (r + 1) - 1 := by
    simpa using congrArg (fun x : ℚ => (x : ℝ)) hq
  have hh : 1 - (∑ j ∈ Finset.range (r + 1), 1 / (2 : ℝ) ^ (j + 1)) =
      1 / (2 : ℝ) ^ (r + 1) := by
    apply (eq_div_iff (by positivity : (2 : ℝ) ^ (r + 1) ≠ 0)).mpr
    nlinarith
  have ht0 : term 0 = 1 := by norm_num [term, Nat.factorial]
  rw [ht0]
  simpa [powerTerm] using hh

lemma rectangle_error_lower (n r : ℕ) :
    1 / (2 : ℝ) ^ (r + 1) <
      (∑' k : ℕ, term k) - (rectangleApprox (n + 1) r : ℝ) := by
  have htail := (partial_sum_error (n + 1)).1
  have hfinite : term 0 - ∑ j ∈ Finset.range (r + 1), powerTerm j 0 ≤
      ∑ k ∈ Finset.range (n + 1),
        (term k - ∑ j ∈ Finset.range (r + 1), powerTerm j k) := by
    exact Finset.single_le_sum (fun k _ => sub_nonneg.mpr (row_partial_le k r)) (by simp)
  rw [first_row_remainder, Finset.sum_sub_distrib, ← cast_rectangleApprox] at hfinite
  linarith

lemma rectangle_reduced_scaled_error_gt_one (n r : ℕ) :
    1 < ((rectangleApprox (n + 1) r).den : ℝ) *
      ((∑' k : ℕ, term k) - (rectangleApprox (n + 1) r : ℝ)) := by
  have hd : (n + 2) ^ (r + 1) ≤ (rectangleApprox (n + 1) r).den :=
    Nat.le_of_dvd (Rat.pos _) (rectangle_den_dvd n r)
  have hd' : (2 : ℝ) ^ (r + 1) ≤ (rectangleApprox (n + 1) r).den := by
    exact_mod_cast (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) (r + 1)).trans hd
  have he := rectangle_error_lower n r
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (r + 1) := by positivity
  have he' : 1 < (2 : ℝ) ^ (r + 1) *
      ((∑' k : ℕ, term k) - (rectangleApprox (n + 1) r : ℝ)) :=
    (div_lt_iff₀ hpos).mp he |>.trans_eq (mul_comm _ _)
  have her : 0 ≤ (∑' k : ℕ, term k) - (rectangleApprox (n + 1) r : ℝ) :=
    ((one_div_pos.mpr hpos).trans he).le
  exact he'.trans_le (mul_le_mul_of_nonneg_right hd' her)

end Erdos68Development

#print axioms Erdos68Development.rectangle_reduced_scaled_error_gt_one
