import FormalConjectures.Util.ProblemImports

/-!
Mean-value ingredients for Dirichlet polynomials.
-/

open Complex Real Set intervalIntegral

noncomputable section

lemma abs_log_sub_ge {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hne : n ≠ m) :
    |Real.log (m : ℝ) - Real.log n| ≥ |(m : ℝ) - n| / (n + m) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rcases lt_trichotomy n m with hnm | hnm | hnm
  · have hnmR : (n : ℝ) < m := Nat.cast_lt.mpr hnm
    have hpos_log : 0 < Real.log m - Real.log n :=
      sub_pos.mpr (Real.log_lt_log hn0 hnmR)
    have hpos_diff : 0 < (m : ℝ) - n := sub_pos.mpr hnmR
    rw [abs_of_pos hpos_log, abs_of_pos hpos_diff]
    have hinteq : Real.log m - Real.log n = ∫ t in (n : ℝ)..m, t⁻¹ := by
      rw [integral_inv_of_pos hn0 hm0, Real.log_div hm0.ne' hn0.ne']
    have hge : ∫ t in (n : ℝ)..m, (m : ℝ)⁻¹ ≤ ∫ t in (n : ℝ)..m, t⁻¹ := by
      refine integral_mono_on (le_of_lt hnmR)
        continuousOn_const.intervalIntegrable ?_ ?_
      · refine (continuousOn_inv₀.mono ?_).intervalIntegrable
        intro t ht
        rw [uIcc_of_le (le_of_lt hnmR)] at ht
        exact (lt_of_lt_of_le hn0 ht.1).ne'
      · intro t ht
        exact inv_anti₀ (lt_of_lt_of_le hn0 ht.1) ht.2
    have hconst : ∫ t in (n : ℝ)..m, (m : ℝ)⁻¹ = ((m : ℝ) - n) * (m : ℝ)⁻¹ := by
      rw [integral_const, smul_eq_mul]
    have hstep : ((m : ℝ) - n) / m ≤ Real.log m - Real.log n := by
      rw [hinteq, div_eq_mul_inv, ← hconst]
      exact hge
    have hden : ((m : ℝ) - n) / (n + m) ≤ ((m : ℝ) - n) / m := by
      refine div_le_div_of_nonneg_left hpos_diff.le hm0 ?_
      linarith
    linarith
  · exact (hne hnm).elim
  · have hnmR : (m : ℝ) < n := Nat.cast_lt.mpr hnm
    have hpos_log : 0 < Real.log n - Real.log m :=
      sub_pos.mpr (Real.log_lt_log hm0 hnmR)
    have hpos_diff : 0 < (n : ℝ) - m := sub_pos.mpr hnmR
    rw [abs_sub_comm (Real.log m), abs_of_pos hpos_log, abs_sub_comm (m : ℝ),
      abs_of_pos hpos_diff, add_comm (n : ℝ)]
    have hinteq : Real.log n - Real.log m = ∫ t in (m : ℝ)..n, t⁻¹ := by
      rw [integral_inv_of_pos hm0 hn0, Real.log_div hn0.ne' hm0.ne']
    have hge : ∫ t in (m : ℝ)..n, (n : ℝ)⁻¹ ≤ ∫ t in (m : ℝ)..n, t⁻¹ := by
      refine integral_mono_on (le_of_lt hnmR)
        continuousOn_const.intervalIntegrable ?_ ?_
      · refine (continuousOn_inv₀.mono ?_).intervalIntegrable
        intro t ht
        rw [uIcc_of_le (le_of_lt hnmR)] at ht
        exact (lt_of_lt_of_le hm0 ht.1).ne'
      · intro t ht
        exact inv_anti₀ (lt_of_lt_of_le hm0 ht.1) ht.2
    have hconst : ∫ t in (m : ℝ)..n, (n : ℝ)⁻¹ = ((n : ℝ) - m) * (n : ℝ)⁻¹ := by
      rw [integral_const, smul_eq_mul]
    have hstep : ((n : ℝ) - m) / n ≤ Real.log n - Real.log m := by
      rw [hinteq, div_eq_mul_inv, ← hconst]
      exact hge
    have hden : ((n : ℝ) - m) / (m + n) ≤ ((n : ℝ) - m) / n := by
      refine div_le_div_of_nonneg_left hpos_diff.le hn0 ?_
      linarith
    linarith

lemma intervalIntegral_exp_mul {T lam : ℝ} :
    ∫ t in (0 : ℝ)..T, Complex.exp (I * lam * t) =
      if lam = 0 then (T : ℂ)
      else (Complex.exp (I * lam * T) - 1) / (I * lam) := by
  by_cases hlam : lam = 0
  · subst hlam
    simp [integral_const]
  · have hc : (I * (lam : ℂ)) ≠ 0 :=
      mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hlam)
    have h := integral_exp_mul_complex (a := (0 : ℝ)) (b := T)
      (c := I * (lam : ℂ)) hc
    simp at h
    have hfun : (fun t : ℝ => Complex.exp (I * lam * t)) =
        (fun t : ℝ => Complex.exp ((I * (lam : ℂ)) * t)) := by
      funext t; simp [mul_assoc]
    rw [if_neg hlam, hfun, h]

lemma abs_integral_exp_mul_le {T lam : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp (I * lam * t)‖ ≤
      if lam = 0 then T else min T (2 / |lam|) := by
  by_cases hlam : lam = 0
  · subst hlam
    simp [integral_const, abs_of_nonneg hT]
  · rw [if_neg hlam]
    have hint := intervalIntegral_exp_mul (T := T) (lam := lam)
    rw [if_neg hlam] at hint
    have hbound : ‖(Complex.exp (I * lam * T) - 1) / (I * lam)‖ ≤ 2 / |lam| := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
      have : ‖Complex.exp (I * lam * T) - 1‖ ≤ 2 := by
        have h := norm_sub_le (Complex.exp (I * lam * T)) (1 : ℂ)
        have h1 : ‖Complex.exp (I * lam * T)‖ = 1 := by
          rw [Complex.norm_exp]
          simp [mul_re, I_re, I_im]
        have : ‖(1 : ℂ)‖ = 1 := by simp
        linarith
      have hpos : 0 < |lam| := abs_pos.mpr hlam
      exact div_le_div_of_nonneg_right this hpos.le
    have hTbound : ‖∫ t in (0 : ℝ)..T, Complex.exp (I * lam * t)‖ ≤ T := by
      refine (norm_integral_le_of_norm_le_const (C := (1 : ℝ)) ?_).trans ?_
      · intro t ht
        have hre : (I * lam * t : ℂ).re = 0 := by
          simp [mul_re, I_re, I_im]
        simp [Complex.norm_exp, hre]
      · simp [abs_of_nonneg hT]
    rw [hint] at hTbound ⊢
    exact le_min hTbound hbound

lemma one_le_abs_cast_sub {n m : ℕ} (hne : n ≠ m) :
    (1 : ℝ) ≤ |(n : ℝ) - m| := by
  have hZ : (1 : ℤ) ≤ |(n : ℤ) - (m : ℤ)| :=
    Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hne))
  have : |(n : ℝ) - (m : ℝ)| = |(n : ℤ) - (m : ℤ)| := by
    rw [← Int.cast_natCast n, ← Int.cast_natCast m, ← Int.cast_sub, Int.cast_abs]
  rw [this]
  exact_mod_cast hZ

/-- Crude pairing: `∑_{n≠m} a n * a m / |n-m| ≤ N ∑ a²`. -/
lemma pairing_crude (a : ℕ → ℝ) (N : ℕ) (_hN : 1 ≤ N)
    (ha : ∀ n, 0 ≤ a n) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (if n = m then (0 : ℝ) else a n * a m / |(n : ℝ) - m|) ≤
      (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, a n ^ 2 := by
  set s := Finset.Icc 1 N
  have h1 : ∀ n ∈ s, ∀ m ∈ s, n ≠ m →
      a n * a m / |(n : ℝ) - m| ≤ a n * a m := by
    intro n hn m hm hne
    have hden := one_le_abs_cast_sub hne
    have hprod : 0 ≤ a n * a m := mul_nonneg (ha n) (ha m)
    have : a n * a m / |(n : ℝ) - m| ≤ a n * a m / 1 :=
      div_le_div_of_nonneg_left hprod (by norm_num) hden
    simpa using this
  have hsum : ∑ n ∈ s, ∑ m ∈ s,
      (if n = m then (0 : ℝ) else a n * a m / |(n : ℝ) - m|) ≤
      ∑ n ∈ s, ∑ m ∈ s, (if n = m then (0 : ℝ) else a n * a m) := by
    refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
    split_ifs with h
    · exact le_rfl
    · exact h1 n hn m hm h
  refine le_trans hsum ?_
  have hsplit : ∑ n ∈ s, ∑ m ∈ s, a n * a m =
      ∑ n ∈ s, ∑ m ∈ s, (if n = m then a n * a m else (0 : ℝ)) +
      ∑ n ∈ s, ∑ m ∈ s, (if n = m then (0 : ℝ) else a n * a m) := by
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    split_ifs <;> ring
  have hmul : ∑ n ∈ s, ∑ m ∈ s, a n * a m = (∑ n ∈ s, a n) * (∑ m ∈ s, a m) :=
    (Finset.sum_mul_sum s s a a).symm
  have hdiag : ∑ n ∈ s, ∑ m ∈ s, (if n = m then a n * a m else (0 : ℝ)) =
      ∑ n ∈ s, a n ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_ite_eq]
    simp [hn, pow_two]
  have hoff : ∑ n ∈ s, ∑ m ∈ s, (if n = m then (0 : ℝ) else a n * a m) =
      (∑ n ∈ s, a n) ^ 2 - ∑ n ∈ s, a n ^ 2 := by
    have : (∑ n ∈ s, a n) * (∑ m ∈ s, a m) = (∑ n ∈ s, a n) ^ 2 := by ring
    linarith
  rw [hoff]
  have hcard : (s.card : ℝ) = (N : ℝ) := by
    simp [s, Nat.card_Icc]
  have hcs : (∑ n ∈ s, a n) ^ 2 ≤ (N : ℝ) * ∑ n ∈ s, a n ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) a
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul] at h
    rw [hcard] at h
    convert h using 1
    ring
  have hsq : 0 ≤ ∑ n ∈ s, a n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

lemma osc_bound {n m : ℕ} {T : ℝ} (hn : 0 < n) (hm : 0 < m) (hne : n ≠ m)
    (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp (I * (Real.log n - Real.log m) * t)‖ ≤
      2 * (n + m : ℝ) / |(n : ℝ) - m| := by
  have hlam : Real.log n - Real.log m ≠ 0 := by
    intro h
    have heq : Real.log n = Real.log m := sub_eq_zero.mp h
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have := (Real.log_injOn_pos (Set.mem_Ioi.mpr hn0) (Set.mem_Ioi.mpr hm0) heq)
    exact hne (Nat.cast_injective this)
  have h := abs_integral_exp_mul_le (T := T) (lam := Real.log n - Real.log m) hT
  rw [if_neg hlam] at h
  have hge := abs_log_sub_ge hn hm hne
  have habs : 0 < |Real.log n - Real.log m| := abs_pos.mpr hlam
  have hnm : 0 < |(n : ℝ) - m| := by
    simp only [abs_pos, ne_eq, sub_eq_zero]
    exact_mod_cast hne
  have hden : 0 < (n + m : ℝ) := by positivity
  have hle : 2 / |Real.log n - Real.log m| ≤ 2 * (n + m : ℝ) / |(n : ℝ) - m| := by
    have hswap : |Real.log (m : ℝ) - Real.log n| = |Real.log n - Real.log m| :=
      abs_sub_comm _ _
    rw [hswap] at hge
    have hstep : |(n : ℝ) - m| / (n + m : ℝ) ≤ |Real.log n - Real.log m| := by
      have : |(m : ℝ) - n| = |(n : ℝ) - m| := abs_sub_comm _ _
      rwa [this] at hge
    have hinv := (inv_le_inv₀ habs (div_pos hnm hden)).mpr hstep
    have hinv' : ((|(n : ℝ) - m| / (n + m : ℝ)))⁻¹ = (n + m : ℝ) / |(n : ℝ) - m| := by
      field
    rw [hinv'] at hinv
    have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
    convert this using 1 <;> field
  have hcast : (Real.log n - Real.log m : ℂ) = ((Real.log n : ℝ) - Real.log m : ℝ) := by
    simp
  simp only [hcast] at h ⊢
  exact h.trans ((min_le_right T _).trans hle)

lemma osc_bound_N {n m N : ℕ} {T : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hnN : n ≤ N) (hmN : m ≤ N) (hne : n ≠ m) (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp (I * (Real.log n - Real.log m) * t)‖ ≤
      4 * N / |(n : ℝ) - m| := by
  have h := osc_bound (n := n) (m := m) (T := T) hn hm hne hT
  refine h.trans ?_
  have hnm : 0 < |(n : ℝ) - m| := by
    simp only [abs_pos, ne_eq, sub_eq_zero]
    exact_mod_cast hne
  have : 2 * (n + m : ℝ) ≤ 4 * N := by
    have : (n : ℝ) ≤ N := Nat.cast_le.mpr hnN
    have : (m : ℝ) ≤ N := Nat.cast_le.mpr hmN
    linarith
  exact div_le_div_of_nonneg_right this hnm.le

end
