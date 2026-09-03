import Submission.GapPhaseMoments

/-! An exact positive divisor expansion for count variances, and subadditivity
in interval length. These are second-order statements, not tail estimates. -/
namespace Erdos970.GapAverages
open Finset

noncomputable def residueDefect (D m : ℕ) : ℝ :=
  (m % D : ℕ) - (m % D : ℕ) ^ 2 / (D : ℝ)

lemma residueDefect_succ (D m : ℕ) (hD : 0 < D) :
    residueDefect D (m + 1) = residueDefect D m + 1 + 2 * (m / D : ℕ) -
      (2 * (m : ℝ) + 1) / D := by
  have hmod := Nat.mod_lt m hD
  have hrel : (m % D : ℕ) + (D : ℝ) * (m / D : ℕ) = m := by
    exact_mod_cast Nat.mod_add_div m D
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hm : (m + 1) % D = (m % D + 1) % D := by simp only [Nat.add_mod, Nat.mod_mod]
  by_cases hs : m % D + 1 < D
  · rw [residueDefect, hm, Nat.mod_eq_of_lt hs, residueDefect]
    push_cast
    field_simp [hDR]
    nlinarith only [hrel]
  · have hs' : m % D + 1 = D := by omega
    have hr : ((m % D : ℕ) : ℝ) + 1 = D := by exact_mod_cast hs'
    rw [residueDefect, hm, hs', Nat.mod_self, residueDefect]
    norm_num only [Nat.cast_zero, zero_pow, zero_div]
    field_simp [hDR]
    nlinarith only [hrel, hr]

/-- The balanced one-residue variance defect is subadditive. -/
lemma residueDefect_subadd (D m n : ℕ) (hD : 0 < D) :
    residueDefect D (m + n) ≤ residueDefect D m + residueDefect D n := by
  have hm := Nat.mod_lt m hD
  have hn := Nat.mod_lt n hD
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hmR : ((m % D : ℕ) : ℝ) < D := by exact_mod_cast hm
  have hnR : ((n % D : ℕ) : ℝ) < D := by exact_mod_cast hn
  by_cases hs : m % D + n % D < D
  · unfold residueDefect
    rw [Nat.add_mod, Nat.mod_eq_of_lt hs]
    push_cast
    apply (mul_le_mul_iff_right₀ hDR).mp
    field_simp
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (m % D))
      (Nat.cast_nonneg (α := ℝ) (n % D))]
  · have hsmall : m % D + n % D - D < D := by omega
    have hsub : D ≤ m % D + n % D := by omega
    unfold residueDefect
    rw [Nat.add_mod, Nat.mod_eq_sub_mod hsub, Nat.mod_eq_of_lt hsmall,
      Nat.cast_sub hsub, Nat.cast_add]
    apply (mul_le_mul_iff_right₀ hDR).mp
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hmR.le) (sub_nonneg.mpr hnR.le)]

lemma sum_pairWeight (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ Q ∈ P.powerset, pairWeight P Q) = density P := by
  have hh := pairKernel_expansion P hP 0
  simp only [dvd_zero, if_true, mul_one] at hh
  rw [← hh]
  unfold pairKernel density
  apply prod_congr rfl
  intro p hp
  simp only [dvd_zero, if_true, mul_one]
  ring

lemma sum_pairKernel_exact (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    (∑ h ∈ range m, pairKernel P (h + 1)) =
      ∑ Q ∈ P.powerset, pairWeight P Q * (m / (∏ p ∈ Q, p) : ℕ) := by
  simp_rw [pairKernel_expansion P hP]
  rw [sum_comm]
  apply sum_congr rfl
  intro Q hQ
  rw [← mul_sum]
  have hc : (∑ h ∈ range m, if (∏ p ∈ Q, p) ∣ h + 1 then (1 : ℝ) else 0) =
      (m / (∏ p ∈ Q, p) : ℕ) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_multiples]
  rw [hc]

lemma phaseMean_count_point_exact (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    phaseMean P (fun r => intervalCount P m r * point P m r) =
      ∑ h ∈ range m, pairKernel P (h + 1) := by
  simp only [intervalCount, sum_mul]
  rw [phaseMean_sum]
  rw [← pairKernel_reverse_sum]
  apply sum_congr rfl
  intro x hx
  exact phaseMean_point_pair P hP x m (mem_range.mp hx).le

noncomputable def countVariance (P : Finset ℕ) (m : ℕ) : ℝ :=
  phaseMean P (fun r => (intervalCount P m r - (m : ℝ) * density P) ^ 2)

lemma countVariance_eq_second (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    countVariance P m = phaseMean P (fun r => intervalCount P m r ^ 2) -
      ((m : ℝ) * density P) ^ 2 := by
  have he (r : Phase P) : (intervalCount P m r - (m : ℝ) * density P) ^ 2 =
      intervalCount P m r ^ 2 - (2 * (m : ℝ) * density P) * intervalCount P m r +
        ((m : ℝ) * density P) ^ 2 := by ring
  unfold countVariance
  simp_rw [he]
  rw [phaseMean_add, phaseMean_sub, phaseMean_mul, phaseMean_count P hP,
    phaseMean_const P hP]
  ring

lemma countVariance_succ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    countVariance P (m + 1) = countVariance P m + density P +
      2 * (∑ h ∈ range m, pairKernel P (h + 1)) - (2 * (m : ℝ) + 1) * density P ^ 2 := by
  have he (r : Phase P) : intervalCount P (m + 1) r ^ 2 =
      intervalCount P m r ^ 2 + 2 * (intervalCount P m r * point P m r) + point P m r := by
    rw [intervalCount_succ]
    nlinarith only [point_sq P m r]
  rw [countVariance_eq_second P hP, countVariance_eq_second P hP]
  simp_rw [he]
  rw [phaseMean_add, phaseMean_add, phaseMean_mul, phaseMean_point P hP,
    phaseMean_count_point_exact P hP]
  push_cast
  ring

/-- Exact variance as a positive combination of balanced residue defects. -/
theorem countVariance_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    countVariance P m = ∑ Q ∈ P.powerset, pairWeight P Q * residueDefect (∏ p ∈ Q, p) m := by
  induction m with
  | zero => simp [countVariance, intervalCount, phaseMean, residueDefect]
  | succ m ih =>
    rw [countVariance_succ P hP, ih, sum_pairKernel_exact P hP,
      ← pairWeight_mass P hP, ← sum_pairWeight P hP]
    rw [← sum_add_distrib, mul_sum, ← sum_add_distrib, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro Q hQ
    have hQP := mem_powerset.mp hQ
    have hD : 0 < ∏ p ∈ Q, p := prod_pos (fun p hp => (hP p (hQP hp)).pos)
    rw [residueDefect_succ _ _ hD]
    simp only [Nat.cast_prod]
    ring

/-- A genuine second-order spatial inequality. It does not imply negative
association of nonlinear functions of adjacent counts. -/
theorem countVariance_subadd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    countVariance P (m + n) ≤ countVariance P m + countVariance P n := by
  simp_rw [countVariance_expansion P hP]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro Q hQ
  have hQP := mem_powerset.mp hQ
  have hD : 0 < ∏ p ∈ Q, p := prod_pos (fun p hp => (hP p (hQP hp)).pos)
  simpa only [mul_add] using mul_le_mul_of_nonneg_left
    (residueDefect_subadd (∏ p ∈ Q, p) m n hD) (pairWeight_nonneg P Q hP)

noncomputable def blockCount (P : Finset ℕ) (a m : ℕ) (r : Phase P) : ℝ :=
  ∑ x ∈ range m, point P (a + x) r

lemma blockCount_add (P : Finset ℕ) (a m n : ℕ) (r : Phase P) :
    blockCount P a (m + n) r = blockCount P a m r + blockCount P (a + m) n r := by
  simp only [blockCount, sum_range_add, Nat.add_assoc]

lemma phaseMean_block (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a m : ℕ) :
    phaseMean P (blockCount P a m) = (m : ℝ) * density P := by
  change phaseMean P (fun r => ∑ x ∈ range m, point P (a + x) r) = _
  rw [phaseMean_sum]
  simp only [phaseMean_point P hP, sum_const, card_range, nsmul_eq_mul]

lemma phaseMean_block_endpoint (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a m : ℕ) :
    phaseMean P (fun r => blockCount P a m r * point P (a + m) r) =
      ∑ h ∈ range m, pairKernel P (h + 1) := by
  simp only [blockCount, sum_mul]
  rw [phaseMean_sum, ← pairKernel_reverse_sum]
  apply sum_congr rfl
  intro x hx
  simpa only [Nat.add_sub_add_left] using phaseMean_point_pair P hP (a + x) (a + m)
    (Nat.add_le_add_left (mem_range.mp hx).le a)

lemma phaseMean_block_sq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a m : ℕ) :
    phaseMean P (fun r => blockCount P a m r ^ 2) =
      phaseMean P (fun r => intervalCount P m r ^ 2) := by
  induction m with
  | zero => simp [blockCount, intervalCount, phaseMean]
  | succ m ih =>
    have hb (r : Phase P) : blockCount P a (m + 1) r ^ 2 =
        blockCount P a m r ^ 2 + 2 * (blockCount P a m r * point P (a + m) r) +
          point P (a + m) r := by
      rw [blockCount, sum_range_succ]
      change (blockCount P a m r + point P (a + m) r) ^ 2 = _
      nlinarith only [point_sq P (a + m) r]
    have hi (r : Phase P) : intervalCount P (m + 1) r ^ 2 =
        intervalCount P m r ^ 2 + 2 * (intervalCount P m r * point P m r) + point P m r := by
      rw [intervalCount_succ]
      nlinarith only [point_sq P m r]
    simp_rw [hb, hi]
    rw [phaseMean_add, phaseMean_add, phaseMean_mul, phaseMean_add, phaseMean_add,
      phaseMean_mul, phaseMean_block_endpoint P hP, phaseMean_count_point_exact P hP,
      phaseMean_point P hP, phaseMean_point P hP, ih]

lemma block_variance_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a m : ℕ) :
    phaseMean P (fun r => (blockCount P a m r - (m : ℝ) * density P) ^ 2) =
      countVariance P m := by
  have he (r : Phase P) : (blockCount P a m r - (m : ℝ) * density P) ^ 2 =
      blockCount P a m r ^ 2 - (2 * (m : ℝ) * density P) * blockCount P a m r +
        ((m : ℝ) * density P) ^ 2 := by ring
  simp_rw [he]
  rw [phaseMean_add, phaseMean_sub, phaseMean_mul, phaseMean_block P hP,
    phaseMean_const P hP, phaseMean_block_sq P hP, countVariance_eq_second P hP]
  ring

/-- Adjacent interval counts have nonpositive covariance. This is a statement
about the counts themselves, not their zero events or exponential transforms. -/
theorem adjacent_count_covariance_nonpos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a m n : ℕ) :
    phaseMean P (fun r => (blockCount P a m r - (m : ℝ) * density P) *
      (blockCount P (a + m) n r - (n : ℝ) * density P)) ≤ 0 := by
  have he (r : Phase P) : (blockCount P a (m + n) r - ((m + n : ℕ) : ℝ) * density P) ^ 2 =
      (blockCount P a m r - (m : ℝ) * density P) ^ 2 +
      (blockCount P (a + m) n r - (n : ℝ) * density P) ^ 2 +
      2 * ((blockCount P a m r - (m : ℝ) * density P) *
        (blockCount P (a + m) n r - (n : ℝ) * density P)) := by
    rw [blockCount_add]
    push_cast
    ring
  have hh := congrArg (phaseMean P) (funext he)
  simp only [phaseMean_add, phaseMean_mul, block_variance_eq P hP] at hh
  have hsub := countVariance_subadd P hP m n
  linarith

#print axioms adjacent_count_covariance_nonpos
#print axioms residueDefect_subadd
#print axioms countVariance_expansion
#print axioms countVariance_subadd
end Erdos970.GapAverages
