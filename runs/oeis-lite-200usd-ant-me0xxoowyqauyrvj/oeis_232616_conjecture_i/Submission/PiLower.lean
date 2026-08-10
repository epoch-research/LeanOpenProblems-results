import Submission.Numeric
open Real ChebLB Cmb
namespace PiLower
noncomputable section
set_option maxRecDepth 8000
set_option linter.unusedTactic false

-- rpow helpers
theorem rpow_half_le (x c : ℝ) (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c^2) : x^((1:ℝ)/2) ≤ c := by
  rw [show ((1:ℝ)/2) = ((2:ℕ):ℝ)⁻¹ by norm_num]
  calc x^(((2:ℕ):ℝ)⁻¹) ≤ (c^2)^(((2:ℕ):ℝ)⁻¹) := Real.rpow_le_rpow hx h (by positivity)
    _ = c := Real.pow_rpow_inv_natCast hc (by norm_num)
theorem rpow_third_le (x c : ℝ) (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c^3) : x^((1:ℝ)/3) ≤ c := by
  rw [show ((1:ℝ)/3) = ((3:ℕ):ℝ)⁻¹ by norm_num]
  calc x^(((3:ℕ):ℝ)⁻¹) ≤ (c^3)^(((3:ℕ):ℝ)⁻¹) := Real.rpow_le_rpow hx h (by positivity)
    _ = c := Real.pow_rpow_inv_natCast hc (by norm_num)

theorem logU_eq : Real.log 13799808 = 7*Real.log 2 + 4*Real.log 3 + 3*Real.log 11 := by
  rw [show (13799808:ℝ) = 2^7*3^4*11^3 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]; push_cast; ring
theorem logt0_eq : Real.log 13860 = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (13860:ℝ) = 2^2*3^2*5*7*11 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]; push_cast; ring
theorem logU_le : Real.log 13799808 ≤ (10275103791/625000000 : ℝ) := by
  rw [logU_eq]; have b2 := Real.log_two_lt_d9; norm_num at b2
  nlinarith [b2, log3_b.2, log11_b.2]
theorem logt0_ge : (47683808803/5000000000 : ℝ) ≤ Real.log 13860 := by
  rw [logt0_eq]; have a2 := Real.log_two_gt_d9; norm_num at a2
  nlinarith [a2, log3_b.1, log5_b.1, log7_b.1, log11_b.1]

theorem hQpos : 0 < Cmb.Q := by norm_num [Cmb.Q]
theorem kset_le : ∀ k ∈ Cmb.kset, k ≤ 13860 := by decide

theorem hxk_t (t : ℝ) (ht : (13860:ℝ) ≤ t) : ∀ k ∈ Cmb.kset, (1:ℝ) ≤ t/k := by
  intro k hk
  have hkpos := Cmb.hk0 k hk
  have hkle := kset_le k hk
  rw [le_div_iff₀ (by exact_mod_cast hkpos)]
  have : (k:ℝ) ≤ 13860 := by exact_mod_cast hkle
  linarith

-- θ at a point t ≥ 13860 dominates thetaLB
theorem thetaLB_le_theta (t : ℝ) (ht : (13860:ℝ) ≤ t) :
    thetaLB Cmb.kset Cmb.acoef Cmb.Q t ≤ Chebyshev.theta t :=
  theta_lower Cmb.kset Cmb.acoef Cmb.Q hQpos Cmb.hk0 Cmb.hsum0 Cmb.hg t (by linarith) (hxk_t t ht)

-- the linear lower bound g(t) = Cl * t - 13805
noncomputable def gfun (t : ℝ) : ℝ := (7086731246918663/7503890625000000 : ℝ) * t - 13805

-- g t ≤ θ t  on [13860, 13799808]
theorem g_le_theta (t : ℝ) (ht : t ∈ Set.Icc (13860:ℝ) 13799808) : gfun t ≤ Chebyshev.theta t := by
  obtain ⟨ht1, ht2⟩ := ht
  have htpos : (0:ℝ) < t := by linarith
  refine le_trans ?_ (thetaLB_le_theta t ht1)
  rw [thetaLB, gfun]
  have hC := Cval_ge
  have hK := Kval_eq
  have hL := Lcval_ge
  have hlogt_le : Real.log t ≤ (10275103791/625000000 : ℝ) :=
    le_trans (Real.log_le_log htpos ht2) logU_le
  have hlogt_pos : (0:ℝ) < Real.log t := by
    have := Real.log_le_log (by norm_num) ht1; have h0 := logt0_ge; linarith
  -- t^(1/2) ≤ sqrtU_hi, t^(1/3) ≤ cbrtU_hi
  have hsq : t^((1:ℝ)/2) ≤ (371481/100 : ℝ) :=
    le_trans (Real.rpow_le_rpow (le_of_lt htpos) ht2 (by norm_num))
      (rpow_half_le _ _ (by norm_num) (by norm_num) (by norm_num))
  have hcb : t^((1:ℝ)/3) ≤ (23986/100 : ℝ) :=
    le_trans (Real.rpow_le_rpow (le_of_lt htpos) ht2 (by norm_num))
      (rpow_third_le _ _ (by norm_num) (by norm_num) (by norm_num))
  have hsqnn : (0:ℝ) ≤ t^((1:ℝ)/2) := Real.rpow_nonneg (le_of_lt htpos) _
  have hcbnn : (0:ℝ) ≤ t^((1:ℝ)/3) := Real.rpow_nonneg (le_of_lt htpos) _
  have hlog4 : Real.log 4 = 2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_lt_d9; norm_num at hl2
  rw [hK, hlog4]
  nlinarith [hC, hL, hlogt_le, hlogt_pos, hsq, hcb, hsqnn, hcbnn, hl2, htpos,
    mul_le_mul hl2.le hsq (by positivity) (by positivity),
    mul_le_mul hlogt_le hcb (by positivity) (by positivity),
    mul_le_mul_of_nonneg_right hC (le_of_lt htpos)]

-- numeric bound for the integrand (E = F = 0)
theorem hbound : ∀ t ∈ Set.Icc (13860:ℝ) 13799808,
    (1747/500000 : ℝ) - (786/5 : ℝ)/t - 0*((1:ℝ)/2)*t^((1:ℝ)/2-1) - 0*((1:ℝ)/3)*t^((1:ℝ)/3-1)
      ≤ gfun t / (t * Real.log t ^ 2) := by
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  have htpos : (0:ℝ) < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hlogt_le : Real.log t ≤ (10275103791/625000000 : ℝ) :=
    le_trans (Real.log_le_log htpos ht2) logU_le
  have hlogt_ge : (47683808803/5000000000 : ℝ) ≤ Real.log t :=
    le_trans logt0_ge (Real.log_le_log (by norm_num) ht1)
  have hlogpos : (0:ℝ) < Real.log t := by linarith
  have hden : (0:ℝ) < t * Real.log t^2 := by positivity
  have hA2 : (1747/500000:ℝ) * Real.log t^2 ≤ (7086731246918663/7503890625000000:ℝ) := by
    nlinarith [hlogt_le, hlogpos]
  have hB2 : (13805:ℝ) ≤ (786/5:ℝ) * Real.log t^2 := by
    nlinarith [hlogt_ge, hlogpos]
  simp only [zero_mul, sub_zero]
  rw [gfun, le_div_iff₀ hden]
  have hexp : ((1747/500000:ℝ) - (786/5:ℝ)/t)*(t*Real.log t^2)
      = (1747/500000:ℝ)*t*Real.log t^2 - (786/5:ℝ)*Real.log t^2 := by
    field_simp
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_right hA2 htpos.le, hB2]

theorem intInt_2_t0 : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t^2))
    MeasureTheory.volume 2 13860 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq 13799808).mono_set
    (Set.Icc_subset_Icc (le_refl _) (by norm_num))
theorem intInt_t0_U : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t^2))
    MeasureTheory.volume 13860 13799808 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq 13799808).mono_set
    (Set.Icc_subset_Icc (by norm_num) (le_refl _))

theorem int_t0_U : (23541443577627/500000000 : ℝ)
    ≤ ∫ t in (13860:ℝ)..13799808, Chebyshev.theta t / (t * Real.log t^2) := by
  have key := integral_theta_lower 13860 13799808 (by norm_num) (by norm_num) gfun g_le_theta
    (1747/500000) (786/5) 0 0 hbound
  simp only [zero_mul, sub_zero] at key
  refine le_trans ?_ key
  have hlU : Real.log 13799808 ≤ (10275103791/625000000:ℝ) := logU_le
  have hlt0 : (47683808803/5000000000:ℝ) ≤ Real.log 13860 := logt0_ge
  nlinarith [hlU, hlt0]

theorem int_2_U : (23541443577627/500000000 : ℝ)
    ≤ ∫ t in (2:ℝ)..13799808, Chebyshev.theta t / (t * Real.log t^2) := by
  have hadd : (∫ t in (2:ℝ)..13799808, Chebyshev.theta t / (t * Real.log t^2))
      = (∫ t in (2:ℝ)..13860, Chebyshev.theta t / (t * Real.log t^2))
        + (∫ t in (13860:ℝ)..13799808, Chebyshev.theta t / (t * Real.log t^2)) :=
    (intervalIntegral.integral_add_adjacent_intervals intInt_2_t0 intInt_t0_U).symm
  rw [hadd]
  have hnn : (0:ℝ) ≤ ∫ t in (2:ℝ)..13860, Chebyshev.theta t / (t * Real.log t^2) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have htp : (0:ℝ) < t := by simp only [Set.mem_Icc] at ht; linarith [ht.1]
    exact div_nonneg (Chebyshev.theta_nonneg t) (mul_nonneg htp.le (sq_nonneg _))
  linarith [int_t0_U, hnn]

theorem thetaU_ge : (63154385972025463856381/4851000000000000 : ℝ) ≤ Chebyshev.theta 13799808 := by
  refine le_trans ?_ (thetaLB_le_theta 13799808 (by norm_num))
  rw [thetaLB, Kval_eq]
  have hC := Cval_ge
  have hL := Lcval_ge
  have hlU := logU_le
  have hl4 : Real.log 4 ≤ (6931471808/5000000000:ℝ) := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    have hl2 := Real.log_two_lt_d9; push_cast; nlinarith [hl2]
  have hsq : (13799808:ℝ)^((1:ℝ)/2) ≤ (371481/100:ℝ) :=
    rpow_half_le _ _ (by norm_num) (by norm_num) (by norm_num)
  have hcb : (13799808:ℝ)^((1:ℝ)/3) ≤ (23986/100:ℝ) :=
    rpow_third_le _ _ (by norm_num) (by norm_num) (by norm_num)
  have hsqnn : (0:ℝ) ≤ (13799808:ℝ)^((1:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
  have hcbnn : (0:ℝ) ≤ (13799808:ℝ)^((1:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
  have hl4nn : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlUpos : (0:ℝ) < Real.log 13799808 := Real.log_pos (by norm_num)
  nlinarith [hC, hL, hlU, hl4, hsq, hcb, hsqnn, hcbnn, hl4nn, hlUpos,
    mul_le_mul hl4 hsq hsqnn (by norm_num : (0:ℝ) ≤ 6931471808/5000000000),
    mul_le_mul hlU hcb hcbnn (by norm_num : (0:ℝ) ≤ 10275103791/625000000),
    mul_le_mul_of_nonneg_right hC (by norm_num : (0:ℝ) ≤ 13799808)]

theorem pi_lower : (833782 : ℕ) ≤ Nat.primeCounting 13799808 := by
  have hpc := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := (13799808:ℝ)) (by norm_num)
  rw [show ⌊(13799808:ℝ)⌋₊ = 13799808 by norm_num] at hpc
  have hlUpos : (0:ℝ) < Real.log 13799808 := Real.log_pos (by norm_num)
  have hth := thetaU_ge
  have hint := int_2_U
  have hdiv : (833782 - 23541443577627/500000000 : ℝ)
      ≤ Chebyshev.theta 13799808 / Real.log 13799808 := by
    rw [le_div_iff₀ hlUpos]
    refine le_trans ?_ hth
    have hlU := logU_le
    nlinarith [mul_le_mul_of_nonneg_left hlU
      (by norm_num : (0:ℝ) ≤ 833782 - 23541443577627/500000000)]
  have hfin : (833782:ℝ) ≤ (Nat.primeCounting 13799808 : ℝ) := by
    rw [hpc]; linarith [hdiv, hint]
  exact_mod_cast hfin

theorem nth_prime_le : Nat.nth Nat.Prime 833781 ≤ 13799808 := by
  by_contra h
  push_neg at h
  have hmono : Nat.primeCounting' 13799809 ≤ 833781 := by
    have := Nat.monotone_primeCounting' (show (13799809:ℕ) ≤ Nat.nth Nat.Prime 833781 by omega)
    rwa [Nat.primeCounting'_nth_eq] at this
  have hpc : (833782:ℕ) ≤ Nat.primeCounting' 13799809 := pi_lower
  omega

end
end PiLower
