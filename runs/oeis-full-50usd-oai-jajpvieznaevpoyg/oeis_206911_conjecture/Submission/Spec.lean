import FormalConjectures.Util.ProblemImports

open Real Nat Finset Filter

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

/-- The number of 3s in the first N terms of the difference sequence D(1), ..., D(N). -/
noncomputable def A206911_count_3s (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

/-- The number of 2s in the first N terms of the difference sequence D(1), ..., D(N). -/
noncomputable def A206911_count_2s (N : ℕ) : ℕ :=
 (range N).sum fun n => if A206911_diff (n + 1) = 2 then 1 else 0

lemma sum_eq_harmonic (n : ℕ) :
    ((range n).sum fun k => 1 / ((k : ℝ) + 1)) = (harmonic n : ℝ) := by
  rw [harmonic]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  congr with k
  norm_num

lemma A_eq (n : ℕ) : A206911 n = n + (Nat.floor (exp (harmonic n : ℝ)) - 1) := by
  unfold A206911
  rw [sum_eq_harmonic]
  simp

lemma exp_harmonic_succ_sub (n : ℕ) :
    exp (harmonic (n+1) : ℝ) - exp (harmonic n : ℝ) =
      exp (harmonic n : ℝ) * (exp (((n+1 : ℕ) : ℝ)⁻¹) - 1) := by
  rw [harmonic_succ]
  norm_num only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
  rw [Real.exp_add]
  ring

lemma exp_harmonic_diff_gt_one (n : ℕ) :
    1 < exp (harmonic (n+1) : ℝ) - exp (harmonic n : ℝ) := by
  rw [exp_harmonic_succ_sub]
  have hn1pos : (0:ℝ) < (n+1:ℕ) := by positivity
  have hlog : Real.log ((n+1:ℕ):ℝ) ≤ (harmonic n : ℝ) := by
    exact_mod_cast log_add_one_le_harmonic n
  have hExpH : ((n+1:ℕ):ℝ) ≤ exp (harmonic n : ℝ) := by
    calc
      ((n+1:ℕ):ℝ) = exp (Real.log ((n+1:ℕ):ℝ)) := by rw [Real.exp_log hn1pos]
      _ ≤ exp (harmonic n : ℝ) := Real.exp_le_exp.mpr hlog
  have hfac : (1:ℝ) / (n+1:ℕ) < exp (((n+1:ℕ):ℝ)⁻¹) - 1 := by
    have hxne : (((n+1:ℕ):ℝ)⁻¹) ≠ 0 := by positivity
    have h := Real.add_one_lt_exp hxne
    have hraw : (((n+1:ℕ):ℝ)⁻¹) < exp (((n+1:ℕ):ℝ)⁻¹) - 1 := by linarith
    simpa [one_div] using hraw
  calc
    (1:ℝ) = ((n+1:ℕ):ℝ) * (1 / (n+1:ℕ) : ℝ) := by field_simp
    _ < exp (harmonic n : ℝ) * (exp (((n+1:ℕ):ℝ)⁻¹) - 1) :=
      mul_lt_mul' hExpH hfac (by positivity) (Real.exp_pos _)

lemma exp_half_lt_five_thirds : exp ((1:ℝ)/2) < 5/3 := by
  have h := Real.exp_bound' (x := (1:ℝ)/2) (n := 5) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith
lemma exp_third_lt_seven_fifths : exp ((1:ℝ)/3) < 7/5 := by
  have h := Real.exp_bound' (x := (1:ℝ)/3) (n := 8) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith
lemma exp_quarter_lt_nine_sevenths : exp ((1:ℝ)/4) < 9/7 := by
  have h := Real.exp_bound' (x := (1:ℝ)/4) (n := 8) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith
lemma exp_fifth_lt_eleven_ninths : exp ((1:ℝ)/5) < 11/9 := by
  have h := Real.exp_bound' (x := (1:ℝ)/5) (n := 8) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith
lemma exp_sixth_lt_six_fifths : exp ((1:ℝ)/6) < 6/5 := by
  have h := Real.exp_bound' (x := (1:ℝ)/6) (n := 8) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith
lemma exp_seventeen_sixty_lt_four_thirds : exp ((17:ℝ)/60) < 4/3 := by
  have h := Real.exp_bound' (x := (17:ℝ)/60) (n := 10) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith
lemma exp_twelfth_lt_eleven_tenths : exp ((1:ℝ)/12) < 11/10 := by
  have h := Real.exp_bound' (x := (1:ℝ)/12) (n := 8) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith
lemma exp_five_sixths_lt_seven_thirds : exp ((5:ℝ)/6) < 7/3 := by
  have h := Real.exp_bound' (x := (5:ℝ)/6) (n := 30) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma exp_harmonic_diff_lt_two_small {n : ℕ} (hn1 : 1 ≤ n) (hn6 : n < 6) :
    exp (harmonic (n+1) : ℝ) - exp (harmonic n : ℝ) < 2 := by
  interval_cases n
  · rw [exp_harmonic_succ_sub]
    norm_num [harmonic_succ, harmonic_zero]
    have hf : exp ((1:ℝ)/2) - 1 < 2/3 := by linarith [exp_half_lt_five_thirds]
    have hfpos : 0 < exp ((1:ℝ)/2) - 1 := by
      have := Real.add_one_lt_exp (show ((1:ℝ)/2) ≠ 0 by norm_num); linarith
    calc
      exp (1:ℝ) * (exp ((1:ℝ)/2) - 1) < 3 * (2/3:ℝ) :=
        mul_lt_mul Real.exp_one_lt_three hf.le hfpos (by positivity)
      _ = 2 := by norm_num
  · rw [exp_harmonic_succ_sub]
    norm_num [harmonic_succ, harmonic_zero]
    have hE : exp ((3:ℝ)/2) < 5 := by
      calc
        exp ((3:ℝ)/2) = exp ((1:ℝ) + 1/2) := by norm_num
        _ = exp (1:ℝ) * exp ((1:ℝ)/2) := by rw [Real.exp_add]
        _ < 3 * (5/3:ℝ) := mul_lt_mul Real.exp_one_lt_three exp_half_lt_five_thirds.le (Real.exp_pos _) (by positivity)
        _ = 5 := by norm_num
    have hf : exp ((1:ℝ)/3) - 1 < 2/5 := by linarith [exp_third_lt_seven_fifths]
    have hfpos : 0 < exp ((1:ℝ)/3) - 1 := by
      have := Real.add_one_lt_exp (show ((1:ℝ)/3) ≠ 0 by norm_num); linarith
    calc
      exp ((3:ℝ)/2) * (exp ((1:ℝ)/3) - 1) < 5 * (2/5:ℝ) :=
        mul_lt_mul hE hf.le hfpos (by positivity)
      _ = 2 := by norm_num
  · rw [exp_harmonic_succ_sub]
    norm_num [harmonic_succ, harmonic_zero]
    have hE : exp ((11:ℝ)/6) < 7 := by
      calc
        exp ((11:ℝ)/6) = exp ((1:ℝ) + 5/6) := by norm_num
        _ = exp (1:ℝ) * exp ((5:ℝ)/6) := by rw [Real.exp_add]
        _ < 3 * (7/3:ℝ) := mul_lt_mul Real.exp_one_lt_three exp_five_sixths_lt_seven_thirds.le (Real.exp_pos _) (by positivity)
        _ = 7 := by norm_num
    have hf : exp ((1:ℝ)/4) - 1 < 2/7 := by linarith [exp_quarter_lt_nine_sevenths]
    have hfpos : 0 < exp ((1:ℝ)/4) - 1 := by
      have := Real.add_one_lt_exp (show ((1:ℝ)/4) ≠ 0 by norm_num); linarith
    calc
      exp ((11:ℝ)/6) * (exp ((1:ℝ)/4) - 1) < 7 * (2/7:ℝ) :=
        mul_lt_mul hE hf.le hfpos (by positivity)
      _ = 2 := by norm_num
  · rw [exp_harmonic_succ_sub]
    norm_num [harmonic_succ, harmonic_zero]
    have hE : exp ((25:ℝ)/12) < 9 := by
      calc
        exp ((25:ℝ)/12) = exp ((1:ℝ) + (1 + 1/12)) := by norm_num
        _ = exp (1:ℝ) * exp ((1:ℝ) + 1/12) := by rw [Real.exp_add]
        _ = exp (1:ℝ) * (exp (1:ℝ) * exp ((1:ℝ)/12)) := by rw [Real.exp_add]
        _ < (68/25:ℝ) * ((68/25:ℝ) * (11/10:ℝ)) := by
          have he : exp (1:ℝ) < (68/25:ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
          have hinner : exp (1:ℝ) * exp ((1:ℝ)/12) < (68/25:ℝ) * (11/10:ℝ) :=
            mul_lt_mul he exp_twelfth_lt_eleven_tenths.le (Real.exp_pos _) (by positivity)
          exact mul_lt_mul he hinner.le (by positivity) (by positivity)
        _ < 9 := by norm_num
    have hf : exp ((1:ℝ)/5) - 1 < 2/9 := by linarith [exp_fifth_lt_eleven_ninths]
    have hfpos : 0 < exp ((1:ℝ)/5) - 1 := by
      have := Real.add_one_lt_exp (show ((1:ℝ)/5) ≠ 0 by norm_num); linarith
    calc
      exp ((25:ℝ)/12) * (exp ((1:ℝ)/5) - 1) < 9 * (2/9:ℝ) :=
        mul_lt_mul hE hf.le hfpos (by positivity)
      _ = 2 := by norm_num
  · rw [exp_harmonic_succ_sub]
    norm_num [harmonic_succ, harmonic_zero]
    have hE : exp ((137:ℝ)/60) < 10 := by
      calc
        exp ((137:ℝ)/60) = exp ((1:ℝ) + (1 + 17/60)) := by norm_num
        _ = exp (1:ℝ) * exp ((1:ℝ) + 17/60) := by rw [Real.exp_add]
        _ = exp (1:ℝ) * (exp (1:ℝ) * exp ((17:ℝ)/60)) := by rw [Real.exp_add]
        _ < (68/25:ℝ) * ((68/25:ℝ) * (4/3:ℝ)) := by
          have he : exp (1:ℝ) < (68/25:ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
          have hinner : exp (1:ℝ) * exp ((17:ℝ)/60) < (68/25:ℝ) * (4/3:ℝ) :=
            mul_lt_mul he exp_seventeen_sixty_lt_four_thirds.le (Real.exp_pos _) (by positivity)
          exact mul_lt_mul he hinner.le (by positivity) (by positivity)
        _ < 10 := by norm_num
    have hf : exp ((1:ℝ)/6) - 1 < 1/5 := by linarith [exp_sixth_lt_six_fifths]
    have hfpos : 0 < exp ((1:ℝ)/6) - 1 := by
      have := Real.add_one_lt_exp (show ((1:ℝ)/6) ≠ 0 by norm_num); linarith
    calc
      exp ((137:ℝ)/60) * (exp ((1:ℝ)/6) - 1) < 10 * (1/5:ℝ) :=
        mul_lt_mul hE hf.le hfpos (by positivity)
      _ = 2 := by norm_num

lemma exp_two_thirds_lt_two : exp ((2:ℝ)/3) < 2 := by
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)).mp
    (lt_trans (by norm_num : (2:ℝ)/3 < 0.6931471803) Real.log_two_gt_d9)

lemma harmonic_lt_log_add_two_thirds {n : ℕ} (hn : 6 ≤ n) :
    (harmonic n : ℝ) < Real.log n + (2:ℝ)/3 := by
  have hanti : Real.eulerMascheroniSeq' n ≤ Real.eulerMascheroniSeq' 6 :=
    Real.strictAnti_eulerMascheroniSeq'.antitone hn
  have h6 : Real.eulerMascheroniSeq' 6 < (2:ℝ)/3 := Real.eulerMascheroniSeq'_six_lt_two_thirds
  have hnz : n ≠ 0 := by omega
  have hseq : Real.eulerMascheroniSeq' n = (harmonic n : ℝ) - Real.log n := by
    simp [Real.eulerMascheroniSeq', hnz]
  have : (harmonic n : ℝ) - Real.log n < (2:ℝ)/3 := by
    rw [← hseq]
    exact lt_of_le_of_lt hanti h6
  linarith

lemma exp_harmonic_diff_lt_two_large {n : ℕ} (hn : 6 ≤ n) :
    exp (harmonic (n+1) : ℝ) - exp (harmonic n : ℝ) < 2 := by
  rw [exp_harmonic_succ_sub]
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hH : (harmonic n : ℝ) < Real.log n + (2:ℝ)/3 := harmonic_lt_log_add_two_thirds hn
  have hExpH : exp (harmonic n : ℝ) < (n:ℝ) * exp ((2:ℝ)/3) := by
    calc
      exp (harmonic n : ℝ) < exp (Real.log (n:ℝ) + (2:ℝ)/3) := Real.exp_lt_exp.mpr hH
      _ = (n:ℝ) * exp ((2:ℝ)/3) := by rw [Real.exp_add, Real.exp_log hnpos]
  have hfac0 : 0 < exp (((n+1 : ℕ) : ℝ)⁻¹) - 1 := by
    have hxpos' : 0 < (((n+1 : ℕ) : ℝ)⁻¹) := by positivity
    have h := Real.add_one_lt_exp (show (((n+1 : ℕ) : ℝ)⁻¹) ≠ 0 by positivity)
    linarith [h, hxpos']
  have hfac : exp (((n+1 : ℕ) : ℝ)⁻¹) - 1 < (1:ℝ) / n := by
    have hxpos : 0 < (((n+1 : ℕ) : ℝ)⁻¹) := by positivity
    have hxlt : (((n+1 : ℕ) : ℝ)⁻¹) < 1 := by
      rw [inv_lt_one₀]
      · exact_mod_cast (by omega : 1 < n + 1)
      · positivity
    have hb := Real.exp_bound_div_one_sub_of_interval' hxpos hxlt
    have hcalc : (1:ℝ) / (1 - (((n+1 : ℕ) : ℝ)⁻¹)) = 1 + (1:ℝ)/n := by
      rw [show (((n+1:ℕ):ℝ)⁻¹) = 1 / ((n:ℝ)+1) by norm_num]
      field_simp [show (n:ℝ) ≠ 0 by positivity, show (n:ℝ)+1 ≠ 0 by positivity]
      ring
    calc
      exp (((n+1 : ℕ) : ℝ)⁻¹) - 1 < (1 / (1 - (((n+1 : ℕ) : ℝ)⁻¹))) - 1 := by linarith
      _ = (1:ℝ) / n := by rw [hcalc]; ring
  calc
    exp (harmonic n : ℝ) * (exp (((n+1 : ℕ) : ℝ)⁻¹) - 1)
        < ((n:ℝ) * exp ((2:ℝ)/3)) * ((1:ℝ)/n) :=
      mul_lt_mul hExpH hfac.le hfac0 (by positivity)
    _ = exp ((2:ℝ)/3) := by field_simp [show (n:ℝ) ≠ 0 by positivity]
    _ < 2 := exp_two_thirds_lt_two

lemma exp_harmonic_diff_lt_two {n : ℕ} (hn1 : 1 ≤ n) :
    exp (harmonic (n+1) : ℝ) - exp (harmonic n : ℝ) < 2 := by
  by_cases h : n < 6
  · exact exp_harmonic_diff_lt_two_small hn1 h
  · exact exp_harmonic_diff_lt_two_large (by omega)

lemma nat_floor_diff_one_or_two {x y : ℝ} (hx0 : 0 ≤ x)
    (hgt : 1 < y - x) (hlt : y - x < 2) :
    Nat.floor y - Nat.floor x = 1 ∨ Nat.floor y - Nat.floor x = 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hxy : x ≤ y := by linarith
  have hxle : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  have hxlt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlow_real : ((Nat.floor x + 1 : ℕ) : ℝ) ≤ y := by norm_num; linarith
  have hlow : Nat.floor x + 1 ≤ Nat.floor y := Nat.le_floor hlow_real
  have hhigh_real : y < ((Nat.floor x + 3 : ℕ) : ℝ) := by norm_num; linarith
  have hhigh : Nat.floor y < Nat.floor x + 3 := (Nat.floor_lt hy0).2 hhigh_real
  omega

lemma floor_exp_harmonic_diff_one_or_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.floor (exp (harmonic (n+1) : ℝ)) - Nat.floor (exp (harmonic n : ℝ)) = 1 ∨
    Nat.floor (exp (harmonic (n+1) : ℝ)) - Nat.floor (exp (harmonic n : ℝ)) = 2 := by
  apply nat_floor_diff_one_or_two (x := exp (harmonic n : ℝ)) (y := exp (harmonic (n+1) : ℝ))
  · exact (Real.exp_pos _).le
  · exact exp_harmonic_diff_gt_one n
  · exact exp_harmonic_diff_lt_two hn

lemma A206911_diff_eq (n : ℕ) (hn : 1 ≤ n) :
    A206911_diff n = 1 + (Nat.floor (exp (harmonic (n+1) : ℝ)) - Nat.floor (exp (harmonic n : ℝ))) := by
  unfold A206911_diff
  rw [A_eq (n+1), A_eq n]
  have hF : Nat.floor (exp (harmonic n : ℝ)) ≤ Nat.floor (exp (harmonic (n+1) : ℝ)) := by
    apply Nat.floor_mono
    rw [← sub_nonneg]
    linarith [exp_harmonic_diff_gt_one n]
  have hFn : 1 ≤ Nat.floor (exp (harmonic n : ℝ)) := by
    apply Nat.le_floor
    norm_num
    rw [harmonic]
    positivity
  omega

lemma A206911_diff_two_or_three (n : ℕ) (hn : 1 ≤ n) :
    A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  rw [A206911_diff_eq n hn]
  rcases floor_exp_harmonic_diff_one_or_two hn with h | h <;> omega


noncomputable def F (n : ℕ) : ℕ := Nat.floor (exp (harmonic n : ℝ))

lemma A_diff_eq_F (n : ℕ) (hn : 1 ≤ n) : A206911_diff n = 1 + (F (n+1) - F n) := by
  simpa [F] using A206911_diff_eq n hn

lemma F_diff_one_or_two {n : ℕ} (hn : 1 ≤ n) :
    F (n+1) - F n = 1 ∨ F (n+1) - F n = 2 := by
  simpa [F] using floor_exp_harmonic_diff_one_or_two hn

lemma count3_succ (N : ℕ) :
    A206911_count_3s (N+1) = A206911_count_3s N + (if A206911_diff (N+1) = 3 then 1 else 0) := by
  unfold A206911_count_3s
  rw [Finset.sum_range_succ]

lemma count2_succ (N : ℕ) :
    A206911_count_2s (N+1) = A206911_count_2s N + (if A206911_diff (N+1) = 2 then 1 else 0) := by
  unfold A206911_count_2s
  rw [Finset.sum_range_succ]

lemma F_growth (N : ℕ) : F 1 + N ≤ F (N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hN : 1 ≤ N+1 := by omega
      rcases F_diff_one_or_two hN with hd | hd <;> omega

lemma count3_formula (N : ℕ) : A206911_count_3s N = F (N+1) - F 1 - N := by
  induction N with
  | zero => simp [A206911_count_3s, F]
  | succ N ih =>
      rw [count3_succ, ih]
      have hN : 1 ≤ N+1 := by omega
      have hA := A_diff_eq_F (N+1) hN
      rcases F_diff_one_or_two hN with hd | hd
      · have hif : (if A206911_diff (N+1) = 3 then 1 else 0) = 0 := by
          simp [hA, hd]
        rw [hif]
        have hg := F_growth N
        omega
      · have hif : (if A206911_diff (N+1) = 3 then 1 else 0) = 1 := by
          simp [hA, hd]
        rw [hif]
        have hg := F_growth N
        omega

lemma F_growth_upper (N : ℕ) : F (N+1) ≤ F 1 + 2*N := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hN : 1 ≤ N+1 := by omega
      rcases F_diff_one_or_two hN with hd | hd <;> omega

lemma count2_formula (N : ℕ) : A206911_count_2s N = 2*N - (F (N+1) - F 1) := by
  induction N with
  | zero => simp [A206911_count_2s]
  | succ N ih =>
      rw [count2_succ, ih]
      have hN : 1 ≤ N+1 := by omega
      have hA := A_diff_eq_F (N+1) hN
      have hg := F_growth N
      have hgu := F_growth_upper N
      rcases F_diff_one_or_two hN with hd | hd
      · have hif : (if A206911_diff (N+1) = 2 then 1 else 0) = 1 := by
          simp [hA, hd]
        rw [hif]
        omega
      · have hif : (if A206911_diff (N+1) = 2 then 1 else 0) = 0 := by
          simp [hA, hd]
        rw [hif]
        omega

lemma tendsto_exp_harmonic_div :
    Tendsto (fun n : ℕ => exp (harmonic n : ℝ) / (n:ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
  have h : Tendsto (fun n : ℕ => exp ((harmonic n : ℝ) - Real.log (n:ℝ))) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
    exact (Real.continuous_exp.continuousAt.tendsto).comp Real.tendsto_harmonic_sub_log
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.exp_sub, Real.exp_log hnpos]

lemma tendsto_F_div : Tendsto (fun n : ℕ => (F n : ℝ) / (n:ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
  have hexp := tendsto_exp_harmonic_div
  have hlowlim : Tendsto (fun n : ℕ => exp (harmonic n : ℝ) / (n:ℝ) - (1:ℝ)/(n:ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
    simpa using hexp.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim hexp ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hlt : exp (harmonic n : ℝ) < (F n : ℝ) + 1 := by simpa [F] using Nat.lt_floor_add_one (exp (harmonic n : ℝ))
    have : exp (harmonic n : ℝ) / (n:ℝ) - (1:ℝ)/(n:ℝ) < (F n : ℝ) / (n:ℝ) := by
      rw [div_sub_div_same]
      rw [div_lt_div_iff_of_pos_right hnpos]
      linarith
    exact this.le
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hle : (F n : ℝ) ≤ exp (harmonic n : ℝ) := by
      simpa [F] using Nat.floor_le (Real.exp_pos (harmonic n : ℝ)).le
    exact div_le_div_of_nonneg_right hle hnpos.le

lemma tendsto_F_succ_div : Tendsto (fun N : ℕ => (F (N+1) : ℝ) / (N:ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
  have h1 : Tendsto (fun N : ℕ => (F (N+1) : ℝ) / ((N+1:ℕ):ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one, add_comm] using tendsto_F_div.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun N : ℕ => (((N+1:ℕ):ℝ) / (N:ℝ))) atTop (nhds (1:ℝ)) := by
    have hbase : Tendsto (fun N : ℕ => (1:ℝ) + (1:ℝ)/(N:ℝ)) atTop (nhds ((1:ℝ)+0)) := by
      exact tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hbase' : Tendsto (fun N : ℕ => (1:ℝ) + (1:ℝ)/(N:ℝ)) atTop (nhds (1:ℝ)) := by simpa using hbase
    refine hbase'.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hN' : (N:ℝ) ≠ 0 := by positivity
    field_simp [hN']
    norm_num
  have hmul := h1.mul hratio
  have hc : exp Real.eulerMascheroniConstant * (1:ℝ) = exp Real.eulerMascheroniConstant := by ring
  rw [hc] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hN' : (N:ℝ) ≠ 0 := by positivity
  field_simp [hN']

lemma tendsto_const_div_nat (a : ℝ) : Tendsto (fun N : ℕ => a / (N:ℝ)) atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) : Tendsto (fun N : ℕ => a * (1 / (N:ℝ))) atTop (nhds (a*0)))

lemma tendsto_count3_div : Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (N:ℝ)) atTop
    (nhds (exp Real.eulerMascheroniConstant - 1)) := by
  have hmain := tendsto_F_succ_div
  have hconst := tendsto_const_div_nat (F 1 : ℝ)
  have hlim : Tendsto (fun N : ℕ => (F (N+1):ℝ)/(N:ℝ) - (F 1:ℝ)/(N:ℝ) - 1) atTop
      (nhds (exp Real.eulerMascheroniConstant - 0 - 1)) := (hmain.sub hconst).sub tendsto_const_nhds
  simpa using hlim.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hform := count3_formula N
    have hg := F_growth N
    have h1 : F 1 ≤ F (N+1) := by omega
    have h2 : N ≤ F (N+1) - F 1 := by omega
    rw [hform]
    have hn : (N:ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
    field_simp [hn])

lemma tendsto_count2_div : Tendsto (fun N : ℕ => (A206911_count_2s N : ℝ) / (N:ℝ)) atTop
    (nhds (2 - exp Real.eulerMascheroniConstant)) := by
  have hmain := tendsto_F_succ_div
  have hconst := tendsto_const_div_nat (F 1 : ℝ)
  have hlim : Tendsto (fun N : ℕ => (2:ℝ) - (F (N+1):ℝ)/(N:ℝ) + (F 1:ℝ)/(N:ℝ)) atTop
      (nhds ((2:ℝ) - exp Real.eulerMascheroniConstant + 0)) := (tendsto_const_nhds.sub hmain).add hconst
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlim.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hform := count2_formula N
    have hg := F_growth N
    have hgu := F_growth_upper N
    have h1 : F 1 ≤ F (N+1) := by omega
    have h2 : F (N+1) - F 1 ≤ 2*N := by omega
    rw [hform]
    have hn : (N:ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
    field_simp [hn]
    norm_num
    ring)

lemma exp_5092_10000_lt : exp ((5092:ℝ)/10000) < 3329/2000 := by
  have h := Real.exp_bound' (x := (5092:ℝ)/10000) (n := 30) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma exp_5091_10000_gt : (1663/1000:ℝ) < exp ((5091:ℝ)/10000) := by
  have h := Real.exp_bound (x := (5091:ℝ)/10000) (n := 20) (by norm_num) (by norm_num)
  rw [abs_sub_le_iff] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma exp_harmonic_1024_upper : exp (harmonic 1024 : ℝ) < (41/23:ℝ)*1024 := by
  have hH : (harmonic 1024 : ℝ) < 75092/10000 := by norm_num [harmonic]
  calc
    exp (harmonic 1024 : ℝ) < exp ((75092:ℝ)/10000) := Real.exp_lt_exp.mpr hH
    _ = exp ((7:ℝ) + 5092/10000) := by norm_num
    _ = exp (1:ℝ)^7 * exp ((5092:ℝ)/10000) := by rw [Real.exp_add, ← Real.exp_nat_mul]; norm_num
    _ < (2.7182818286:ℝ)^7 * (3329/2000:ℝ) := by
      apply mul_lt_mul ?_ exp_5092_10000_lt.le (Real.exp_pos _) (by positivity)
      exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos _).le (by norm_num)
    _ < (41/23:ℝ)*1024 := by norm_num

lemma exp_harmonic_1024_lower : (16/9:ℝ)*1025 < exp (harmonic 1024 : ℝ) := by
  have hH : (75091/10000 : ℝ) < (harmonic 1024 : ℝ) := by norm_num [harmonic]
  calc
    (16/9:ℝ)*1025 < (2.7182818283:ℝ)^7 * (1663/1000:ℝ) := by norm_num
    _ < exp (1:ℝ)^7 * exp ((5091:ℝ)/10000) := by
      apply mul_lt_mul ?_ exp_5091_10000_gt.le (by positivity) (by positivity)
      exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
    _ = exp ((75091:ℝ)/10000) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    _ < exp (harmonic 1024 : ℝ) := Real.exp_lt_exp.mpr hH

lemma exp_gamma_lower : (16/9:ℝ) < exp Real.eulerMascheroniConstant := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1024
  have h_expseq : exp (Real.eulerMascheroniSeq 1024) < exp Real.eulerMascheroniConstant := Real.exp_lt_exp.mpr hseq
  have hleft : (16/9:ℝ) < exp (Real.eulerMascheroniSeq 1024) := by
    have h := exp_harmonic_1024_lower
    have hpos : (0:ℝ) < ((1024:ℕ):ℝ) + 1 := by norm_num
    unfold Real.eulerMascheroniSeq
    rw [Real.exp_sub, Real.exp_log hpos]
    rw [lt_div_iff₀ hpos]
    convert h using 1 <;> norm_num
  exact lt_trans hleft h_expseq

lemma exp_gamma_upper : exp Real.eulerMascheroniConstant < (41/23:ℝ) := by
  have hseq := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  have h_expseq : exp Real.eulerMascheroniConstant < exp (Real.eulerMascheroniSeq' 1024) := Real.exp_lt_exp.mpr hseq
  have hright : exp (Real.eulerMascheroniSeq' 1024) < (41/23:ℝ) := by
    have h := exp_harmonic_1024_upper
    have hpos : (0:ℝ) < 1024 := by norm_num
    have hseqeq : Real.eulerMascheroniSeq' 1024 = (harmonic 1024 : ℝ) - Real.log (1024:ℝ) := by
      simp only [Real.eulerMascheroniSeq', OfNat.ofNat_ne_zero, ↓reduceIte]
      ring_nf
    rw [hseqeq, Real.exp_sub, Real.exp_log hpos]
    rw [div_lt_iff₀ hpos]
    exact h
  exact lt_trans h_expseq hright

lemma tendsto_ratio_counts :
    Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop
      (nhds ((exp Real.eulerMascheroniConstant - 1) / (2 - exp Real.eulerMascheroniConstant))) := by
  have h3 := tendsto_count3_div
  have h2 := tendsto_count2_div
  have h2ne : 2 - exp Real.eulerMascheroniConstant ≠ 0 := by
    have hu := exp_gamma_upper
    linarith
  have hdiv := h3.div h2 h2ne
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℕ), h2.eventually_ne h2ne] with N hN hdenN
  have hn : (N:ℝ) ≠ 0 := by positivity
  have hc2 : (A206911_count_2s N : ℝ) ≠ 0 := by
    intro hc
    apply hdenN
    simp [hc]
  change ((A206911_count_3s N : ℝ) / (N:ℝ)) / ((A206911_count_2s N : ℝ) / (N:ℝ)) =
      (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)
  rw [div_div_div_cancel_right₀ hn]

lemma ratio_limit_in_interval :
    (35/10 : ℝ) < ((exp Real.eulerMascheroniConstant - 1) / (2 - exp Real.eulerMascheroniConstant)) ∧
    ((exp Real.eulerMascheroniConstant - 1) / (2 - exp Real.eulerMascheroniConstant)) < (36/10 : ℝ) := by
  constructor
  · have hl := exp_gamma_lower
    have hu := exp_gamma_upper
    have hden : 0 < 2 - exp Real.eulerMascheroniConstant := by linarith
    rw [lt_div_iff₀ hden]
    nlinarith
  · have hu := exp_gamma_upper
    have hden : 0 < 2 - exp Real.eulerMascheroniConstant := by linarith
    rw [div_lt_iff₀ hden]
    nlinarith

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
:= by
  constructor
  · exact A206911_diff_two_or_three
  · refine ⟨(exp Real.eulerMascheroniConstant - 1) / (2 - exp Real.eulerMascheroniConstant), ?_, ?_, tendsto_ratio_counts⟩
    · exact ratio_limit_in_interval.1
    · exact ratio_limit_in_interval.2
