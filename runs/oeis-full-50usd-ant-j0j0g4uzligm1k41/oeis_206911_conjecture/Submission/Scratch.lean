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
