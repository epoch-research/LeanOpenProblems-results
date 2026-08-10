import FormalConjectures.Util.ProblemImports

open Real Nat Finset Filter Topology

-- TRAP: for y ≥ 1, log y ≤ y/2 - 1/(2y)
theorem log_le_trap (y : ℝ) (hy : 1 ≤ y) : Real.log y ≤ y / 2 - 1 / (2 * y) := by
  set f : ℝ → ℝ := fun y => y / 2 - 1 / (2 * y) - Real.log y with hf
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f ((x - 1)^2 / (2 * x^2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => y / 2) (1/2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have h2 : HasDerivAt (fun y : ℝ => 1 / (2 * y)) (-(1/(2*x^2))) x := by
      have hh : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul 2
      have h2ne : (2:ℝ) * x ≠ 0 := by positivity
      have := (hh.inv h2ne)
      simp only [one_div]
      convert this using 1
      field_simp
    have h3 : HasDerivAt (fun y : ℝ => Real.log y) (1/x) x := by
      simpa using Real.hasDerivAt_log (ne_of_gt hx)
    have := (h1.sub h2).sub h3
    convert this using 1
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (f' := fun x => (x - 1)^2 / (2 * x^2))
    · intro x hx
      exact ((hderiv x (lt_of_lt_of_le one_pos hx)).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x (lt_trans one_pos hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans one_pos hx
      positivity
  have h0 : f 1 = 0 := by simp [hf]
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hy) hy
  rw [h0] at this
  simp only [hf] at this
  linarith

-- MID: for y ≥ 1, 2*(y-1)/(y+1) ≤ log y
theorem log_ge_mid (y : ℝ) (hy : 1 ≤ y) : 2 * (y - 1) / (y + 1) ≤ Real.log y := by
  set f : ℝ → ℝ := fun y => Real.log y - 2 * (y - 1) / (y + 1) with hf
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f ((x - 1)^2 / (x * (x+1)^2)) x := by
    intro x hx
    have hxp1 : (0:ℝ) < x + 1 := by linarith
    have h3 : HasDerivAt (fun y : ℝ => Real.log y) (1/x) x := by
      simpa using Real.hasDerivAt_log (ne_of_gt hx)
    have hnum : HasDerivAt (fun y : ℝ => 2 * (y - 1)) 2 x := by
      have : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
        simpa using (hasDerivAt_id x).sub_const 1
      simpa using this.const_mul 2
    have hden : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
      simpa using (hasDerivAt_id x).add_const 1
    have hdne : x + 1 ≠ 0 := ne_of_gt hxp1
    have hquot := hnum.div hden hdne
    have := h3.sub hquot
    convert this using 1
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (f' := fun x => (x - 1)^2 / (x * (x+1)^2))
    · intro x hx
      exact ((hderiv x (lt_of_lt_of_le one_pos hx)).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x (lt_trans one_pos hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans one_pos hx
      positivity
  have h0 : f 1 = 0 := by simp [hf]
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hy) hy
  rw [h0] at this
  simp only [hf] at this
  linarith

noncomputable def Cseq : ℕ → ℝ := fun n => (harmonic n : ℝ) - Real.log n - 1/(2*n)
noncomputable def Dseq : ℕ → ℝ := fun n => (harmonic n : ℝ) - Real.log (n + 1/2)

-- trapezoid step: for n ≥ 1
theorem C_step (n : ℕ) (hn : 1 ≤ n) : Cseq n ≤ Cseq (n+1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n:ℝ)+1) - Real.log n ≤ (2*n+1)/(2*n*(n+1)) := by
    have hy : (1:ℝ) ≤ ((n:ℝ)+1)/n := by
      rw [le_div_iff₀ hn0]; linarith
    have := log_le_trap (((n:ℝ)+1)/n) hy
    rw [Real.log_div (by positivity) (by positivity)] at this
    have heq : ((n:ℝ)+1)/n/2 - 1/(2*(((n:ℝ)+1)/n)) = (2*n+1)/(2*n*(n+1)) := by
      field_simp; ring
    rw [heq] at this
    exact this
  simp only [Cseq]
  have hh : (harmonic (n+1) : ℝ) = (harmonic n : ℝ) + 1/((n:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  rw [hh]
  push_cast
  have : Real.log ((n:ℝ)+1) - Real.log n ≤ (2*n+1)/(2*n*(n+1)) := hlog
  have hsplit : (2*(n:ℝ)+1)/(2*n*(n+1)) = 1/(2*n) + 1/(2*(n+1)) := by
    field_simp; ring
  rw [hsplit] at this
  -- goal: harmonic n - log n - 1/(2n) ≤ harmonic n + 1/(n+1) - log(n+1) - 1/(2(n+1))
  have hfrac : 1/((n:ℝ)+1) - 1/(2*((n:ℝ)+1)) = 1/(2*((n:ℝ)+1)) := by
    field_simp; ring
  linarith

theorem D_step (n : ℕ) : Dseq (n+1) ≤ Dseq n := by
  have h1 : (0:ℝ) < (n:ℝ) + 1/2 := by positivity
  have h2 : (0:ℝ) < (n:ℝ) + 3/2 := by positivity
  have hlog : (1:ℝ)/((n:ℝ)+1) ≤ Real.log ((n:ℝ)+3/2) - Real.log ((n:ℝ)+1/2) := by
    have hy : (1:ℝ) ≤ ((n:ℝ)+3/2)/((n:ℝ)+1/2) := by
      rw [le_div_iff₀ h1]; linarith
    have := log_ge_mid (((n:ℝ)+3/2)/((n:ℝ)+1/2)) hy
    rw [Real.log_div (by positivity) (by positivity)] at this
    have heq : 2 * (((n:ℝ)+3/2)/((n:ℝ)+1/2) - 1) / (((n:ℝ)+3/2)/((n:ℝ)+1/2) + 1) = 1/((n:ℝ)+1) := by
      field_simp; ring
    rw [heq] at this
    exact this
  simp only [Dseq]
  have hh : (harmonic (n+1) : ℝ) = (harmonic n : ℝ) + 1/((n:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  rw [hh]
  have hcast : ((n:ℝ)+1) + 1/2 = (n:ℝ) + 3/2 := by ring
  push_cast
  rw [show ((n:ℝ)+1+1/2) = (n:ℝ)+3/2 by ring]
  linarith

theorem C_tendsto : Tendsto Cseq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ => (1:ℝ)/(2*(n:ℝ))) atTop (𝓝 0) := by
    have h0 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/2 : ℝ)
    rw [mul_zero] at h0
    convert h0 using 2 with n
    ring
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  have : Cseq = fun n : ℕ => ((harmonic n : ℝ) - Real.log n) - 1/(2*(n:ℝ)) := by
    ext n; simp only [Cseq]
  rw [this]; exact h3

theorem D_tendsto : Tendsto Dseq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  -- Dseq n = (harmonic n - log n) - (log(n+1/2) - log n) = (harmonic n - log n) - log((n+1/2)/n)
  have h2 : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1/2) - Real.log n) atTop (𝓝 0) := by
    -- ratio tends to 1
    have hr : Tendsto (fun n : ℕ => ((n:ℝ)+1/2)/(n:ℝ)) atTop (𝓝 1) := by
      have hz : Tendsto (fun n : ℕ => (1:ℝ)/(2*(n:ℝ))) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/2 : ℝ)
        rw [mul_zero] at h0
        convert h0 using 2 with n
        ring
      have := hz.const_add 1
      rw [add_zero] at this
      apply this.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
    have hlog : Tendsto (fun n : ℕ => Real.log (((n:ℝ)+1/2)/(n:ℝ))) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num)).tendsto.comp hr
    rw [Real.log_one] at hlog
    apply hlog.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    rw [Real.log_div (by positivity) (by positivity)]
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  have : Dseq = fun n : ℕ => ((harmonic n : ℝ) - Real.log n)
      - (Real.log ((n:ℝ)+1/2) - Real.log n) := by
    ext n; simp only [Dseq]; ring
  rw [this]; exact h3

-- log bounds
theorem log_three_upper : Real.log 3 ≤ 10987/10000 := by
  have h := Real.log_div_le_sum_range_add (x := (1/2 : ℝ)) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_five_lower : (16093/10000 : ℝ) ≤ Real.log 5 := by
  have h := Real.sum_range_le_log_div (x := (2/3 : ℝ)) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem Cseq_mono : Monotone Cseq := by
  apply monotone_nat_of_le_succ
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Cseq]
    norm_num
  · exact C_step n hn

theorem Dseq_anti : Antitone Dseq := by
  apply antitone_nat_of_succ_le
  intro n
  exact D_step n

theorem gamma_lb : (5762/10000 : ℝ) < Real.eulerMascheroniConstant := by
  have hle : Cseq 12 ≤ Real.eulerMascheroniConstant := Cseq_mono.ge_of_tendsto C_tendsto 12
  have hh12 : (harmonic 12 : ℝ) = 86021/27720 := by
    simp only [harmonic, Finset.sum_range_succ]; norm_num
  have e12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12:ℝ) = 2^2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h3u : Real.log 3 ≤ 10987/10000 := log_three_upper
  have hcval : Cseq 12 = (86021/27720 : ℝ) - Real.log 12 - 1/(2*12) := by
    simp only [Cseq]; rw [hh12]; norm_num
  rw [hcval, e12] at hle
  linarith

theorem gamma_ub : Real.eulerMascheroniConstant < (5778/10000 : ℝ) := by
  have hle : Real.eulerMascheroniConstant ≤ Dseq 12 := Dseq_anti.le_of_tendsto D_tendsto 12
  have hh12 : (harmonic 12 : ℝ) = 86021/27720 := by
    simp only [harmonic, Finset.sum_range_succ]; norm_num
  have e125 : Real.log (12 + 1/2) = 2 * Real.log 5 - Real.log 2 := by
    rw [show (12 + 1/2:ℝ) = 5^2 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h5l : (16093/10000 : ℝ) ≤ Real.log 5 := log_five_lower
  have hdval : Dseq 12 = (86021/27720 : ℝ) - Real.log (12 + 1/2) := by
    simp only [Dseq]; rw [hh12]; norm_num
  rw [hdval, e125] at hle
  linarith

-- ===== Padé bound =====
theorem psi_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1 - (1 - t) * Real.exp t := by
  set ψ : ℝ → ℝ := fun t => 1 - (1 - t) * Real.exp t with hψ
  have hd : ∀ x : ℝ, HasDerivAt ψ (x * Real.exp x) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (1 - t) * Real.exp t) ((-1) * Real.exp x + (1-x) * Real.exp x) x := by
      apply HasDerivAt.mul
      · simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
      · exact Real.hasDerivAt_exp x
    have : HasDerivAt ψ (0 - ((-1) * Real.exp x + (1-x)*Real.exp x)) x :=
      HasDerivAt.sub (hasDerivAt_const x (1:ℝ)) h1
    convert this using 1; ring
  have hmono : MonotoneOn ψ (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun x => x * Real.exp x)
    · intro x hx; exact (hd x).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx; have : 0 ≤ x := le_of_lt hx; positivity
  have h0 : ψ 0 = 0 := by simp [hψ]
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr ht) ht
  rw [h0] at this; simpa [hψ] using this

theorem exp_pade (t : ℝ) (ht : 0 ≤ t) : Real.exp t * (2 - t) ≤ 2 + t := by
  set g : ℝ → ℝ := fun t => 2 + t - (2 - t) * Real.exp t with hg
  have hd : ∀ x : ℝ, HasDerivAt g (1 - (1 - x) * Real.exp x) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (2 - t) * Real.exp t) ((-1) * Real.exp x + (2-x)*Real.exp x) x := by
      apply HasDerivAt.mul
      · simpa using (hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x)
      · exact Real.hasDerivAt_exp x
    have h2 : HasDerivAt (fun t : ℝ => 2 + t) 1 x := by
      simpa using (hasDerivAt_const x (2:ℝ)).add (hasDerivAt_id x)
    have := h2.sub h1
    convert this using 1; ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun x => 1 - (1-x)*Real.exp x)
    · intro x hx; exact (hd x).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx; exact psi_nonneg x (le_of_lt hx)
  have h0 : g 0 = 0 := by simp [hg]
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr ht) ht
  rw [h0] at this; simp only [hg] at this; linarith

-- ===== Part 1 analytic core =====
noncomputable def E : ℕ → ℝ := fun n => Real.exp (harmonic n : ℝ)

theorem E_pos (n : ℕ) : 0 < E n := Real.exp_pos _
theorem E_rec (n : ℕ) : E (n+1) = E n * Real.exp (1/((n:ℝ)+1)) := by
  simp only [E]; rw [← Real.exp_add]; congr 1; rw [harmonic_succ]; push_cast; ring

theorem E_upper (n : ℕ) : E n < Real.exp Real.eulerMascheroniConstant * ((n:ℝ)+1) := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simp only [Real.eulerMascheroniSeq] at h
  have hlog : (harmonic n : ℝ) < Real.eulerMascheroniConstant + Real.log ((n:ℝ)+1) := by linarith
  simp only [E]
  calc Real.exp (harmonic n : ℝ) < Real.exp (Real.eulerMascheroniConstant + Real.log ((n:ℝ)+1)) :=
        Real.exp_lt_exp.mpr hlog
    _ = Real.exp Real.eulerMascheroniConstant * ((n:ℝ)+1) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]

theorem E_lower (n : ℕ) (hn : 1 ≤ n) : Real.exp Real.eulerMascheroniConstant * (n:ℝ) < E n := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have hn0 : n ≠ 0 := by omega
  simp only [Real.eulerMascheroniSeq', hn0, if_false] at h
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hlog : Real.eulerMascheroniConstant + Real.log (n:ℝ) < (harmonic n : ℝ) := by linarith
  simp only [E]
  calc Real.exp Real.eulerMascheroniConstant * (n:ℝ)
        = Real.exp (Real.eulerMascheroniConstant + Real.log (n:ℝ)) := by
          rw [Real.exp_add, Real.exp_log hnpos]
    _ < Real.exp (harmonic n : ℝ) := Real.exp_lt_exp.mpr hlog

-- exp gamma bounds
theorem expγ_lb : (3/2:ℝ) < Real.exp Real.eulerMascheroniConstant := by
  have hhalf := Real.one_half_lt_eulerMascheroniConstant
  have h1 : Real.exp (1/2) < Real.exp Real.eulerMascheroniConstant := Real.exp_lt_exp.mpr hhalf
  have h2 := Real.add_one_le_exp (1/2 : ℝ)
  linarith

theorem expγ_ub : Real.exp Real.eulerMascheroniConstant < 181255/100000 := by
  have hub := gamma_ub
  have hhalf := Real.one_half_lt_eulerMascheroniConstant
  have hpade := exp_pade Real.eulerMascheroniConstant (le_of_lt (lt_trans (by norm_num) hhalf))
  have h2 : (0:ℝ) < 2 - Real.eulerMascheroniConstant := by linarith
  nlinarith [hpade, h2, hub, Real.exp_pos Real.eulerMascheroniConstant]

-- small exp bounds
theorem exp_one_lt3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
theorem exp_32_lt5 : Real.exp (3/2) < 5 := by
  have hsq : Real.exp (3/2) ^ 2 < 5 ^ 2 := by
    have e1 : Real.exp (3/2) ^ 2 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    rw [e1]
    calc Real.exp 1 ^ 3 < (2.7182818286:ℝ) ^ 3 := by gcongr; exact Real.exp_one_lt_d9
      _ < 5 ^ 2 := by norm_num
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
theorem exp_116_lt7 : Real.exp (11/6) < 7 := by
  have hsq : Real.exp (11/6) ^ 6 < 7 ^ 6 := by
    have e1 : Real.exp (11/6) ^ 6 = Real.exp 1 ^ 11 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    rw [e1]
    calc Real.exp 1 ^ 11 < (2.7182818286:ℝ) ^ 11 := by gcongr; exact Real.exp_one_lt_d9
      _ < 7 ^ 6 := by norm_num
  exact lt_of_pow_lt_pow_left₀ 6 (by norm_num) hsq
theorem exp_2512_lt9 : Real.exp (25/12) < 9 := by
  have hsq : Real.exp (25/12) ^ 12 < 9 ^ 12 := by
    have e1 : Real.exp (25/12) ^ 12 = Real.exp 1 ^ 25 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    rw [e1]
    calc Real.exp 1 ^ 25 < (2.7182818286:ℝ) ^ 25 := by gcongr; exact Real.exp_one_lt_d9
      _ < 9 ^ 12 := by norm_num
  exact lt_of_pow_lt_pow_left₀ 12 (by norm_num) hsq

theorem E_ub2 (n : ℕ) (hn : 1 ≤ n) : E n < 2*(n:ℝ)+1 := by
  rcases Nat.lt_or_ge n 5 with h4 | h5
  · interval_cases n
    · have hv : (harmonic 1:ℝ) = 1 := by norm_num [harmonic, Finset.sum_range_succ]
      simp only [E, hv]; norm_num; exact exp_one_lt3
    · have hv : (harmonic 2:ℝ) = 3/2 := by norm_num [harmonic, Finset.sum_range_succ]
      simp only [E, hv]; norm_num; exact exp_32_lt5
    · have hv : (harmonic 3:ℝ) = 11/6 := by norm_num [harmonic, Finset.sum_range_succ]
      simp only [E, hv]; norm_num; exact exp_116_lt7
    · have hv : (harmonic 4:ℝ) = 25/12 := by norm_num [harmonic, Finset.sum_range_succ]
      simp only [E, hv]; norm_num; exact exp_2512_lt9
  · have hub := E_upper n
    have hexp := expγ_ub
    have hn5 : (5:ℝ) ≤ (n:ℝ) := by exact_mod_cast h5
    have h1 : Real.exp Real.eulerMascheroniConstant * ((n:ℝ)+1) < (181255/100000)*((n:ℝ)+1) := by
      apply mul_lt_mul_of_pos_right hexp; positivity
    have h2 : (181255/100000:ℝ)*((n:ℝ)+1) ≤ 2*(n:ℝ)+1 := by nlinarith [hn5]
    linarith

theorem E_lb2 (n : ℕ) (hn : 1 ≤ n) : (n:ℝ)+1 ≤ E n := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · rw [← h1]
    have hv : (harmonic 1:ℝ) = 1 := by norm_num [harmonic, Finset.sum_range_succ]
    simp only [E, hv]; push_cast; norm_num
    have := Real.exp_one_gt_d9; linarith
  · have hlow := E_lower n hn
    have hexp := expγ_lb
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2
    have h3 : (3/2:ℝ) * (n:ℝ) < Real.exp Real.eulerMascheroniConstant * (n:ℝ) :=
      mul_lt_mul_of_pos_right hexp hn0
    have h4 : (n:ℝ)+1 ≤ (3/2:ℝ)*(n:ℝ) := by linarith
    linarith

theorem g_lb (n : ℕ) (hn : 1 ≤ n) : 1 ≤ E (n+1) - E n := by
  rw [E_rec n]
  have hEpos := E_pos n
  have hElb := E_lb2 n hn
  have hnpos : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hd1 := Real.add_one_le_exp (1/((n:ℝ)+1))
  have key2 : E n * (1/((n:ℝ)+1)) + E n ≤ E n * Real.exp (1/((n:ℝ)+1)) := by
    have h := mul_le_mul_of_nonneg_left hd1 hEpos.le
    nlinarith [h]
  have key3 : (1:ℝ) ≤ E n * (1/((n:ℝ)+1)) := by
    rw [mul_one_div, le_div_iff₀ hnpos, one_mul]; exact hElb
  linarith [key2, key3]

theorem g_ub (n : ℕ) (hn : 1 ≤ n) : E (n+1) - E n < 2 := by
  have hnpos : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hp := exp_pade (1/((n:ℝ)+1)) (by positivity)
  have h2t : (0:ℝ) < 2 - 1/((n:ℝ)+1) := by
    have : 1/((n:ℝ)+1) ≤ 1 := by rw [div_le_one hnpos]; linarith
    linarith
  have hle : Real.exp (1/((n:ℝ)+1)) ≤ (2 + 1/((n:ℝ)+1))/(2 - 1/((n:ℝ)+1)) := by
    rw [le_div_iff₀ h2t]; exact hp
  have hval : (2 + 1/((n:ℝ)+1))/(2 - 1/((n:ℝ)+1)) = (2*(n:ℝ)+3)/(2*(n:ℝ)+1) := by
    have hn0 : (n:ℝ)+1 ≠ 0 := ne_of_gt hnpos
    have h21 : (2*(n:ℝ)+1) ≠ 0 := by positivity
    have h2t' : 2 - 1/((n:ℝ)+1) ≠ 0 := ne_of_gt h2t
    rw [div_eq_div_iff h2t' h21]
    field_simp
    ring
  rw [hval] at hle
  have hpb : Real.exp (1/((n:ℝ)+1)) - 1 ≤ 2/(2*(n:ℝ)+1) := by
    have heq : (2*(n:ℝ)+3)/(2*(n:ℝ)+1) - 1 = 2/(2*(n:ℝ)+1) := by
      have : (2*(n:ℝ)+1) ≠ 0 := by positivity
      field_simp; ring
    linarith [hle, heq]
  rw [E_rec n]
  have hEpos := E_pos n
  have hEub := E_ub2 n hn
  have step1 : E n * Real.exp (1/((n:ℝ)+1)) - E n = E n * (Real.exp (1/((n:ℝ)+1)) - 1) := by ring
  rw [step1]
  have step2 : E n * (Real.exp (1/((n:ℝ)+1)) - 1) ≤ E n * (2/(2*(n:ℝ)+1)) :=
    mul_le_mul_of_nonneg_left hpb hEpos.le
  have h21 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
  have step3 : E n * (2/(2*(n:ℝ)+1)) < 2 := by
    rw [show E n * (2/(2*(n:ℝ)+1)) = E n * 2 / (2*(n:ℝ)+1) by ring, div_lt_iff₀ h21]
    linarith [hEub]
  linarith [step2, step3]

-- ===== Floor lemma & Part 1 =====
theorem floor_diff (a b : ℝ) (h1 : 1 ≤ b - a) (h2 : b - a < 2) :
    ⌊b⌋ - ⌊a⌋ = 1 ∨ ⌊b⌋ - ⌊a⌋ = 2 := by
  have hge : ⌊a⌋ + 1 ≤ ⌊b⌋ := by
    apply Int.le_floor.mpr; push_cast; have := Int.floor_le a; linarith
  have hle : ⌊b⌋ < ⌊a⌋ + 3 := by
    have hb : (⌊b⌋ : ℝ) < (⌊a⌋ : ℝ) + 3 := by
      have h3 := Int.lt_floor_add_one a; have h4 := Int.floor_le b; linarith
    exact_mod_cast hb
  omega

/--
A206911: Position of $n$-th partial sum of the harmonic series when all the partial sums are jointly ranked with the set $\{\log(k+1)\}$; complement of A206912.
The $n$-th term $a(n)$ is the rank of $S(n) = \sum_{i=1}^n 1/i$ in the sorted list.
This rank is computed as $n + \lfloor \exp(S(n)) - 1 \rfloor$.
-/
noncomputable def A206911 (n : ℕ) : ℕ :=
  -- Define $S_n = \sum_{k=1}^n \frac{1}{k}$
  let S_n_real : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

  -- Count of log terms is $\lfloor e^{S_n} - 1 \rfloor$
  let count_log_terms : ℤ := floor (exp S_n_real - 1)

  -- Final rank: n + count.
  n + count_log_terms.toNat

/-- The difference sequence D(n) = A206911(n+1) - A206911(n), indexed starting at n=1. -/
noncomputable def A206911_diff (n : ℕ) : ℕ := A206911 (n + 1) - A206911 n

theorem Sval (m : ℕ) : ((range m).sum fun k => 1 / ((k : ℝ) + 1)) = (harmonic m : ℝ) := by
  rw [harmonic]; push_cast; apply Finset.sum_congr rfl; intro k _; rw [one_div]

theorem A_eq (m : ℕ) : A206911 m = m + (⌊E m - 1⌋).toNat := by
  simp only [A206911, Sval m, E]
  rw [Int.toNat_natCast, Int.floor_toNat]

theorem harmonic_nonneg_real (m : ℕ) : (0:ℝ) ≤ (harmonic m : ℝ) := by
  rw [← Sval m]; positivity

theorem fl_nonneg (m : ℕ) : (0:ℤ) ≤ ⌊E m - 1⌋ := by
  apply Int.le_floor.mpr
  push_cast
  have : (1:ℝ) ≤ E m := by
    simp only [E]; exact Real.one_le_exp_iff.mpr (harmonic_nonneg_real m)
  linarith

theorem part1 (n : ℕ) (hn : 1 ≤ n) : A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  have hfd := floor_diff (E n - 1) (E (n+1) - 1)
    (by have := g_lb n hn; linarith) (by have := g_ub n hn; linarith)
  have hfa := fl_nonneg n
  have hfb := fl_nonneg (n+1)
  rw [A206911_diff, A_eq, A_eq]
  rcases hfd with h | h
  · left; omega
  · right; omega

-- ===== Part 2: monotonicity & identities =====
theorem E_mono (m : ℕ) : E m ≤ E (m+1) := by
  simp only [E]
  apply Real.exp_le_exp.mpr
  rw [harmonic_succ]; push_cast
  have : (0:ℝ) ≤ ((m:ℝ)+1)⁻¹ := by positivity
  linarith

theorem A_mono (m : ℕ) : A206911 m ≤ A206911 (m+1) := by
  rw [A_eq, A_eq]
  have hfl : ⌊E m - 1⌋ ≤ ⌊E (m+1) - 1⌋ := Int.floor_mono (by linarith [E_mono m])
  have : (⌊E m - 1⌋).toNat ≤ (⌊E (m+1) - 1⌋).toNat := Int.toNat_le_toNat hfl
  omega

theorem diff_int (m : ℕ) : (A206911_diff m : ℤ) = (A206911 (m+1) : ℤ) - (A206911 m : ℤ) := by
  rw [A206911_diff, Nat.cast_sub (A_mono m)]

theorem A1_eq : A206911 1 = 2 := by
  rw [A_eq]
  have hE1 : E 1 = Real.exp 1 := by
    simp only [E]; congr 1; norm_num [harmonic, Finset.sum_range_succ]
  have hfloor : ⌊E 1 - 1⌋ = 1 := by
    rw [hE1, Int.floor_eq_iff]
    constructor
    · push_cast; have := Real.exp_one_gt_d9; linarith
    · push_cast; have := exp_one_lt3; linarith
  rw [hfloor]; norm_num

/-- The number of 3s in the first N terms of the difference sequence D(1), ..., D(N). -/
noncomputable def A206911_count_3s (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

/-- The number of 2s in the first N terms of the difference sequence D(1), ..., D(N). -/
noncomputable def A206911_count_2s (N : ℕ) : ℕ :=
 (range N).sum fun n => if A206911_diff (n + 1) = 2 then 1 else 0

theorem hsum (N : ℕ) : A206911_count_3s N + A206911_count_2s N = N := by
  have hpt : ∀ n ∈ range N,
      (if A206911_diff (n+1) = 3 then 1 else 0) + (if A206911_diff (n+1) = 2 then 1 else 0) = 1 := by
    intro n _
    rcases part1 (n+1) (by omega) with h | h <;> simp [h]
  rw [A206911_count_3s, A206911_count_2s, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem htel (N : ℕ) :
    2*(A206911_count_2s N : ℤ) + 3*(A206911_count_3s N : ℤ) = (A206911 (N+1) : ℤ) - 2 := by
  have step : 2*(A206911_count_2s N : ℤ) + 3*(A206911_count_3s N : ℤ)
      = ∑ n ∈ range N, ((A206911 (n+2) : ℤ) - (A206911 (n+1) : ℤ)) := by
    rw [A206911_count_2s, A206911_count_3s]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hd : (A206911 (n+2) : ℤ) - (A206911 (n+1) : ℤ) = (A206911_diff (n+1) : ℤ) := by
      rw [diff_int (n+1)]
    rw [hd]
    rcases part1 (n+1) (by omega) with h | h <;> simp [h]
  rw [step]
  have := Finset.sum_range_sub (fun i => (A206911 (i+1) : ℤ)) N
  simp only at this
  rw [this, A1_eq]
  norm_num

-- ===== Part 2: limit =====
theorem count3_eq (N : ℕ) : (A206911_count_3s N : ℤ) = (A206911 (N+1):ℤ) - 2 - 2*N := by
  have h1z : (A206911_count_3s N : ℤ) + (A206911_count_2s N : ℤ) = N := by exact_mod_cast hsum N
  have h2 := htel N
  linarith

theorem count2_eq (N : ℕ) : (A206911_count_2s N : ℤ) = 3*N - ((A206911 (N+1):ℤ) - 2) := by
  have h1z : (A206911_count_3s N : ℤ) + (A206911_count_2s N : ℤ) = N := by exact_mod_cast hsum N
  have h2 := htel N
  linarith

noncomputable def fr (N : ℕ) : ℝ := (⌊E (N+1) - 1⌋ : ℝ)

theorem A_real (N : ℕ) : (A206911 (N+1) : ℝ) = ((N:ℝ)+1) + fr N := by
  rw [A_eq]; push_cast
  simp only [fr]
  have hc : (⌊E (N+1) - 1⌋.toNat : ℝ) = (⌊E (N+1) - 1⌋ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (fl_nonneg (N+1))
  rw [hc]

-- E(N+1)/(N+1) → exp γ
theorem hE1N : Tendsto (fun N : ℕ => E (N+1) / ((N:ℝ)+1)) atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have hreindex : Tendsto (fun N:ℕ => (harmonic (N+1):ℝ) - Real.log ((N:ℝ)+1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    have h := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    apply h.congr
    intro N
    simp only [Function.comp]
    push_cast
    ring
  have hexp := (Real.continuous_exp.tendsto _).comp hreindex
  apply hexp.congr
  intro N
  simp only [Function.comp, E]
  rw [Real.exp_sub, Real.exp_log (by positivity)]

theorem exp_5762_gt : (16/9 : ℝ) < Real.exp (5762/10000) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 5762/10000) 6
  have : (16/9 : ℝ) < ∑ i ∈ Finset.range 6, (5762/10000:ℝ)^i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

theorem exp_5778_lt : Real.exp (5778/10000) < 41/23 := by
  have h := Real.exp_bound' (x := (5778/10000 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 6, (5778/10000:ℝ)^m / m.factorial)
      + (5778/10000:ℝ)^6 * (6+1) / ((6:ℕ).factorial * 6) < 41/23 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

theorem expγ_gt : (16/9 : ℝ) < Real.exp Real.eulerMascheroniConstant := by
  have h1 := Real.exp_lt_exp.mpr gamma_lb
  have h2 := exp_5762_gt
  linarith

theorem expγ_lt : Real.exp Real.eulerMascheroniConstant < 41/23 := by
  have h1 := Real.exp_lt_exp.mpr gamma_ub
  have h2 := exp_5778_lt
  linarith

theorem hn1_lim : Tendsto (fun N:ℕ => ((N:ℝ)+1)/(N:ℝ)) atTop (𝓝 1) := by
  have hz := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h := hz.const_add 1
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

theorem hEN : Tendsto (fun N:ℕ => E (N+1)/(N:ℝ)) atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have h := hE1N.mul hn1_lim
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hN1 : ((N:ℝ)+1) ≠ 0 := by positivity
  field_simp

theorem hfrN : Tendsto (fun N:ℕ => fr N/(N:ℝ)) atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have hg : Tendsto (fun N:ℕ => (2:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2:ℝ)
    rw [mul_zero] at this
    apply this.congr; intro N; ring
  have hdiff : Tendsto (fun N:ℕ => fr N/(N:ℝ) - E (N+1)/(N:ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm ?_ hg
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
      rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hN0]
      have hab : |fr N - E (N+1)| ≤ 2 := by
        have h1 : fr N ≤ E (N+1) - 1 := by simp only [fr]; exact Int.floor_le _
        have h2 : E (N+1) - 1 < fr N + 1 := by simp only [fr]; exact Int.lt_floor_add_one _
        rw [abs_le]; constructor <;> linarith
      gcongr
  have := hEN.add hdiff
  rw [add_zero] at this
  apply this.congr; intro N; ring

theorem hw : Tendsto (fun N:ℕ => (A206911 (N+1):ℝ)/(N:ℝ)) atTop
    (𝓝 (1 + Real.exp Real.eulerMascheroniConstant)) := by
  have h := hn1_lim.add hfrN
  have heq : (fun N:ℕ => (A206911 (N+1):ℝ)/(N:ℝ))
      = (fun N:ℕ => ((N:ℝ)+1)/(N:ℝ) + fr N/(N:ℝ)) := by
    ext N; rw [A_real N, div_add_div_same]
  rw [heq]; exact h

theorem h2N_lim : Tendsto (fun N:ℕ => (2:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
  have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2:ℝ)
  rw [mul_zero] at this
  apply this.congr; intro N; ring

theorem part2 : ∃ L : ℝ, (35/10:ℝ) < L ∧ L < (36/10:ℝ) ∧
    Tendsto (fun N:ℕ => (A206911_count_3s N:ℝ)/(A206911_count_2s N:ℝ)) atTop (𝓝 L) := by
  set g := Real.exp Real.eulerMascheroniConstant with hgdef
  have hglt : g < 41/23 := expγ_lt
  have hggt : (16/9:ℝ) < g := expγ_gt
  have hg2 : (2:ℝ) - g > 0 := by linarith
  refine ⟨(g-1)/(2-g), ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hg2]; linarith
  · rw [div_lt_iff₀ hg2]; linarith
  · have hnum : Tendsto (fun N:ℕ => (A206911 (N+1):ℝ)/N - 2/N - 2) atTop (𝓝 (g - 1)) := by
      have h := (hw.sub h2N_lim).sub_const 2
      convert h using 2
      rw [hgdef]; ring
    have hden : Tendsto (fun N:ℕ => 3 - (A206911 (N+1):ℝ)/N + 2/N) atTop (𝓝 (2 - g)) := by
      have h := (tendsto_const_nhds (x := (3:ℝ)) (f := atTop) |>.sub hw).add h2N_lim
      convert h using 2
      rw [hgdef]; ring
    have hdiv := hnum.div hden (by linarith)
    apply hdiv.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hc3 : (A206911_count_3s N : ℝ) = (A206911 (N+1):ℝ) - 2 - 2*(N:ℝ) := by
      exact_mod_cast count3_eq N
    have hc2 : (A206911_count_2s N : ℝ) = 3*(N:ℝ) - ((A206911 (N+1):ℝ) - 2) := by
      exact_mod_cast count2_eq N
    simp only [Pi.div_apply]
    rw [hc3, hc2]
    have en : (A206911 (N+1):ℝ)/N - 2/N - 2 = ((A206911 (N+1):ℝ)-2-2*(N:ℝ))/(N:ℝ) := by
      field_simp
    have ed : (3:ℝ) - (A206911 (N+1):ℝ)/N + 2/N
        = (3*(N:ℝ)-((A206911 (N+1):ℝ)-2))/(N:ℝ) := by
      field_simp; ring
    rw [en, ed, div_div_div_cancel_right₀]
    exact hN0

/--
Conjecture: the difference sequence of A206911 consists of 2s and 3s, and the ratio (number of 3s)/(number of 2s) tends to a number between 3.5 and 3.6.
-/
theorem oeis_206911_conjecture :
  -- Part 1: The difference sequence consists of 2s and 3s for n ≥ 1.
  (∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) ∧

  -- Part 2: The ratio of counts of 3s to 2s tends to a limit L in (3.5, 3.6).
  (∃ L : ℝ,
     (35/10 : ℝ) < L ∧ L < (36/10 : ℝ) ∧
     Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds L))
:= ⟨part1, part2⟩

