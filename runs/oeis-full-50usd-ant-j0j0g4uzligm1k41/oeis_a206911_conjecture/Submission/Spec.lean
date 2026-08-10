import FormalConjectures.Util.ProblemImports

open Real Nat Finset Filter Topology

set_option maxRecDepth 10000

/--
A206911: Position of $n$-th partial sum of the harmonic series when all the partial sums are jointly ranked with the set $\{\log(k+1)\}$; complement of A206912.
The $n$-th term $a(n)$ is the rank of $S(n) = \sum_{i=1}^n 1/i$ in the sorted list.
This rank is computed as $n + \lfloor \exp(S(n)) - 1 \rfloor$.
-/
noncomputable def A206911 (n : ℕ) : ℕ :=
  -- Define $S_n = \sum_{k=1}^n \frac{1}{k}$
  let S_n_real : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

  -- The number of log terms less than S_n is $\lfloor e^{S_n} - 1 \rfloor$.
  let count_log_terms : ℤ := floor (exp S_n_real - 1)

  -- Final rank: n + count.
  n + count_log_terms.toNat

-- Formalization of the conjecture.

/-- The difference sequence of A206911. Always an integer, should be 2 or 3 based on the conjecture. -/
noncomputable def A206911_diff (n : ℕ) : ℤ :=
  (A206911 (n + 1) : ℤ) - (A206911 n : ℤ)

/-- The number of times the difference sequence is 3, for indices $k \in \{1, \dots, N\}$. -/
noncomputable def count_threes (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

/-- The number of terms considered is $N$. Assuming the difference is 2 or 3 for all $k \in \{1, \dots, N\}$,
the number of 2s is $N$ minus the number of 3s. -/
noncomputable def count_twos (N : ℕ) : ℕ :=
  N - count_threes N

/-- The ratio of the number of 3s to the number of 2s in the difference sequence up to index $N$. -/
noncomputable def ratio_threes_to_twos (N : ℕ) : ℝ :=
  if count_twos N = 0 then 0
  else (count_threes N : ℝ) / (count_twos N : ℝ)

/-! ### Auxiliary lemmas for settling the conjecture -/

noncomputable def ff (n : ℕ) : ℤ := ⌊Real.exp (harmonic n : ℝ)⌋

-- S_n_real equals harmonic n
theorem hharm (n : ℕ) : ((range n).sum fun k => 1 / ((k : ℝ) + 1)) = (harmonic n : ℝ) := by
  rw [harmonic]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [one_div]

theorem harmonic_nonneg (n : ℕ) : (0:ℝ) ≤ (harmonic n : ℝ) := by
  rw [← hharm]
  apply Finset.sum_nonneg
  intro k _
  positivity

theorem ff_ge_one (n : ℕ) : 1 ≤ ff n := by
  rw [ff, Int.le_floor]
  push_cast
  calc (1:ℝ) = Real.exp 0 := by rw [Real.exp_zero]
    _ ≤ _ := Real.exp_le_exp.2 (harmonic_nonneg n)

theorem A206911_eq (n : ℕ) : (A206911 n : ℤ) = n + ff n - 1 := by
  have : A206911 n = n + (⌊Real.exp ((range n).sum fun k => 1 / ((k : ℝ) + 1)) - 1⌋).toNat := rfl
  rw [this]
  rw [hharm]
  have hfloor : (⌊Real.exp (harmonic n : ℝ) - 1⌋ : ℤ) = ff n - 1 := by
    rw [ff]
    rw [show (1:ℝ) = ((1:ℤ):ℝ) by norm_num, Int.floor_sub_intCast]
  rw [hfloor]
  have hnn : (0:ℤ) ≤ ff n - 1 := by have := ff_ge_one n; omega
  push_cast
  rw [Int.toNat_of_nonneg hnn]
  ring

theorem diff_eq (n : ℕ) : A206911_diff n = 1 + ff (n+1) - ff n := by
  rw [A206911_diff, A206911_eq, A206911_eq]
  push_cast
  ring

noncomputable def E : ℝ := Real.exp Real.eulerMascheroniConstant

/-- Upper bound: exp(H_n) < (n+1) E, for all n. -/
theorem exp_harm_lt (n : ℕ) : Real.exp (harmonic n : ℝ) < ((n : ℝ) + 1) * E := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  rw [Real.eulerMascheroniSeq] at h
  have hlt : (harmonic n : ℝ) < Real.eulerMascheroniConstant + Real.log ((n:ℝ) + 1) := by linarith
  calc Real.exp (harmonic n : ℝ)
      < Real.exp (Real.eulerMascheroniConstant + Real.log ((n:ℝ) + 1)) := Real.exp_lt_exp.2 hlt
    _ = E * ((n:ℝ)+1) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
        rw [E]
    _ = ((n:ℝ)+1) * E := by ring

/-- Lower bound: n E < exp(H_n), for n ≥ 1. -/
theorem exp_harm_gt (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * E < Real.exp (harmonic n : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq', if_neg (by omega)] at h
  have hgt : Real.eulerMascheroniConstant + Real.log (n:ℝ) < (harmonic n : ℝ) := by linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  calc (n : ℝ) * E = E * (n:ℝ) := by ring
    _ = Real.exp (Real.eulerMascheroniConstant + Real.log (n:ℝ)) := by
        rw [Real.exp_add, Real.exp_log hnpos, E]
    _ < Real.exp (harmonic n : ℝ) := Real.exp_lt_exp.2 hgt

/-- exp(H_n) ≥ n+1 from log(n+1) ≤ H_n. -/
theorem exp_harm_ge_succ (n : ℕ) : ((n : ℝ) + 1) ≤ Real.exp (harmonic n : ℝ) := by
  have h := log_add_one_le_harmonic n
  have : Real.log ((n:ℝ)+1) ≤ (harmonic n : ℝ) := by
    convert h using 2
    push_cast; ring
  calc ((n:ℝ)+1) = Real.exp (Real.log ((n:ℝ)+1)) := by rw [Real.exp_log (by positivity)]
    _ ≤ Real.exp (harmonic n : ℝ) := Real.exp_le_exp.2 this

theorem gamma_lt : Real.eulerMascheroniConstant < 5778/10000 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  rw [Real.eulerMascheroniSeq', if_neg (by norm_num)] at h
  have hH : (harmonic 1024 : ℝ) < 750918/100000 := by
    have hq : harmonic 1024 < (750918/100000 : ℚ) := by
      norm_num [harmonic, Finset.sum_range_succ]
    have h2 : (harmonic 1024 : ℝ) < ((750918/100000 : ℚ) : ℝ) := by exact_mod_cast hq
    rwa [show ((750918/100000 : ℚ) : ℝ) = 750918/100000 by push_cast; ring] at h2
  have hlog : Real.log ((1024:ℕ):ℝ) = 10 * Real.log 2 := by
    rw [show ((1024:ℕ):ℝ) = 2^10 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : (6931471803/10000000000:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  rw [hlog] at h
  linarith

theorem gamma_gt : (5767/10000:ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1024
  rw [Real.eulerMascheroniSeq] at h
  have hH : (750917/100000:ℝ) < (harmonic 1024 : ℝ) := by
    have hq : (750917/100000 : ℚ) < harmonic 1024 := by
      norm_num [harmonic, Finset.sum_range_succ]
    have h2 : ((750917/100000 : ℚ) : ℝ) < (harmonic 1024 : ℝ) := by exact_mod_cast hq
    rwa [show ((750917/100000 : ℚ) : ℝ) = 750917/100000 by push_cast; ring] at h2
  have hlog2 : Real.log 2 < 6931471808/10000000000 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have h1025 : Real.log (((1024:ℕ):ℝ) + 1) ≤ 10 * Real.log 2 + 1/1024 := by
    have e : (((1024:ℕ):ℝ) + 1) = 1024 * (1025/1024) := by push_cast; ring
    rw [e, Real.log_mul (by norm_num) (by norm_num)]
    have hl1 : Real.log (1024:ℝ) = 10 * Real.log 2 := by
      rw [show (1024:ℝ) = 2^10 by norm_num, Real.log_pow]; push_cast; ring
    have hl2 : Real.log (1025/1024 : ℝ) ≤ 1/1024 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1025/1024 by norm_num)
      linarith
    rw [hl1]; linarith
  have hLog1025 : Real.log (((1024:ℕ):ℝ) + 1) < 69324484/10000000 := by
    linarith [h1025, hlog2]
  have step : (5767/10000:ℝ) < (harmonic 1024 : ℝ) - Real.log (((1024:ℕ):ℝ) + 1) := by
    linarith [hH, hLog1025]
  exact step.trans h

theorem E_lt : E < 41/23 := by
  have hγ : Real.eulerMascheroniConstant < 5778/10000 := gamma_lt
  have hE : E < Real.exp (5778/10000) := by rw [E]; exact Real.exp_lt_exp.2 hγ
  refine hE.trans ?_
  have hb := Real.exp_bound' (x:=(5778/10000:ℝ)) (by norm_num) (by norm_num) (n:=8) (by norm_num)
  refine hb.trans_lt ?_
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

theorem E_gt : (16:ℝ)/9 < E := by
  have hγ : (5767/10000:ℝ) < Real.eulerMascheroniConstant := gamma_gt
  have hE : Real.exp (5767/10000) < E := by rw [E]; exact Real.exp_lt_exp.2 hγ
  refine lt_trans ?_ hE
  have hb := Real.sum_le_exp_of_nonneg (x:=(5767/10000:ℝ)) (by norm_num) 8
  refine lt_of_lt_of_le ?_ hb
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

theorem exp_half_lt : Real.exp (1/2) < 165/100 := by
  have hb := Real.exp_bound' (x:=(1/2:ℝ)) (by norm_num) (by norm_num) (n:=6) (by norm_num)
  refine hb.trans_lt ?_
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

theorem exp_56_lt : Real.exp (5/6) < 231/100 := by
  have hb := Real.exp_bound' (x:=(5/6:ℝ)) (by norm_num) (by norm_num) (n:=8) (by norm_num)
  refine hb.trans_lt ?_
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- exp(H_n) < 2n+1 for n ≥ 1. -/
theorem expH_lt (n : ℕ) (hn : 1 ≤ n) : Real.exp (harmonic n : ℝ) < 2*(n:ℝ)+1 := by
  rcases lt_or_ge n 4 with hsmall | hbig
  · interval_cases n
    · -- n = 1, harmonic 1 = 1
      have : (harmonic 1 : ℝ) = 1 := by norm_num [harmonic, Finset.sum_range_succ]
      rw [this]; push_cast
      have := Real.exp_one_lt_d9; linarith
    · -- n = 2, harmonic 2 = 3/2
      have hh : (harmonic 2 : ℝ) = 3/2 := by norm_num [harmonic, Finset.sum_range_succ]
      rw [hh]
      have e32 : Real.exp (3/2) = Real.exp 1 * Real.exp (1/2) := by
        rw [← Real.exp_add]; norm_num
      have h1 := Real.exp_one_lt_d9
      have h2 := exp_half_lt
      rw [show ((2:ℕ):ℝ) = 2 by norm_num, e32]
      nlinarith [h1, h2, Real.exp_pos (1:ℝ), Real.exp_pos (1/2:ℝ)]
    · -- n = 3, harmonic 3 = 11/6
      have hh : (harmonic 3 : ℝ) = 11/6 := by norm_num [harmonic, Finset.sum_range_succ]
      rw [hh]
      have e116 : Real.exp (11/6) = Real.exp 1 * Real.exp (5/6) := by
        rw [← Real.exp_add]; norm_num
      have h1 := Real.exp_one_lt_d9
      have h2 := exp_56_lt
      rw [show ((3:ℕ):ℝ) = 3 by norm_num, e116]
      nlinarith [h1, h2, Real.exp_pos (1:ℝ), Real.exp_pos (5/6:ℝ)]
  · have h1 := exp_harm_lt n
    have h2 := E_lt
    have hn4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hbig
    have hnp : (0:ℝ) ≤ (n:ℝ)+1 := by positivity
    nlinarith [h1, h2, hn4, hnp, mul_nonneg hnp (le_of_lt (show (0:ℝ) < 41/23 - E by linarith))]

/-- Padé-type bound: for t ∈ [0,1], (2 - t) exp t ≤ 2 + t. -/
theorem pade (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (2 - t) * Real.exp t ≤ 2 + t := by
  have hb := Real.exp_bound' ht0 ht1 (n:=4) (by norm_num)
  have hexp : Real.exp t ≤ 1 + t + t^2/2 + t^3/6 + 5*t^4/96 := by
    refine hb.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    ring
  have h2t : (0:ℝ) ≤ 2 - t := by linarith
  nlinarith [hexp, mul_nonneg h2t (sub_nonneg.mpr hexp), pow_nonneg ht0 3, pow_nonneg ht0 4,
    pow_nonneg ht0 5, Real.exp_pos t]

theorem harmonic_succ_real (n : ℕ) :
    (harmonic (n+1) : ℝ) = (harmonic n : ℝ) + 1/((n:ℝ)+1) := by
  rw [harmonic_succ]; push_cast; ring

/-- Δ ≥ 1 : exp(H_n) + 1 ≤ exp(H_{n+1}), for all n. -/
theorem delta_ge (n : ℕ) :
    Real.exp (harmonic n : ℝ) + 1 ≤ Real.exp (harmonic (n+1) : ℝ) := by
  rw [harmonic_succ_real, Real.exp_add]
  set a := Real.exp (harmonic n : ℝ) with ha
  set t := 1/((n:ℝ)+1) with ht
  have hnpos : (0:ℝ) < (n:ℝ)+1 := by positivity
  have htpos : 0 < t := by rw [ht]; positivity
  have hexp_t : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have hapos : 0 < a := Real.exp_pos _
  have hge : ((n:ℝ)+1) ≤ a := exp_harm_ge_succ n
  have hat : ((n:ℝ)+1) * t = 1 := by rw [ht]; field_simp
  nlinarith [mul_le_mul_of_nonneg_left hexp_t hapos.le,
    mul_le_mul_of_nonneg_right hge htpos.le, hat]

/-- Δ < 2 : exp(H_{n+1}) < exp(H_n) + 2, for n ≥ 1. -/
theorem delta_lt (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (harmonic (n+1) : ℝ) < Real.exp (harmonic n : ℝ) + 2 := by
  rw [harmonic_succ_real, Real.exp_add]
  set a := Real.exp (harmonic n : ℝ) with ha
  set t := 1/((n:ℝ)+1) with ht
  have hnpos : (0:ℝ) < (n:ℝ)+1 := by positivity
  have htpos : 0 < t := by rw [ht]; positivity
  have htle : t ≤ 1 := by
    rw [ht, div_le_one hnpos]; linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]
  have h2t : (0:ℝ) < 2 - t := by linarith
  have hapos : 0 < a := Real.exp_pos _
  have hpade := pade t htpos.le htle
  have ha2 : a < 2*(n:ℝ)+1 := expH_lt n hn
  have htkey : t*(a+1) < 2 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_lt_iff₀ hnpos]; linarith [ha2]
  have hstep1 : a*((2-t)*Real.exp t) ≤ a*(2+t) := mul_le_mul_of_nonneg_left hpade hapos.le
  have hstep2 : a*(2+t) < (a+2)*(2-t) := by nlinarith [htkey]
  have hchain : a*((2-t)*Real.exp t) < (a+2)*(2-t) := lt_of_le_of_lt hstep1 hstep2
  have hcomb : (a*Real.exp t)*(2-t) < (a+2)*(2-t) := by
    have heq : a*((2-t)*Real.exp t) = (a*Real.exp t)*(2-t) := by ring
    linarith [hchain, heq]
  exact lt_of_mul_lt_mul_right hcomb h2t.le

theorem increment_ge (n : ℕ) : ff n + 1 ≤ ff (n+1) := by
  rw [ff, ff]
  have h := delta_ge n
  calc ⌊Real.exp (harmonic n : ℝ)⌋ + 1
      = ⌊Real.exp (harmonic n : ℝ) + 1⌋ := by rw [Int.floor_add_one]
    _ ≤ ⌊Real.exp (harmonic (n+1) : ℝ)⌋ := Int.floor_mono h

theorem increment_le (n : ℕ) (hn : 1 ≤ n) : ff (n+1) ≤ ff n + 2 := by
  rw [ff, ff]
  have h := delta_lt n hn
  have hb : (⌊Real.exp (harmonic (n+1) : ℝ)⌋ : ℝ) ≤ Real.exp (harmonic (n+1) : ℝ) := Int.floor_le _
  have ha : Real.exp (harmonic n : ℝ) < (⌊Real.exp (harmonic n : ℝ)⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hcast : (⌊Real.exp (harmonic (n+1) : ℝ)⌋ : ℝ) < (⌊Real.exp (harmonic n : ℝ)⌋ : ℝ) + 3 := by
    linarith
  have hint : ⌊Real.exp (harmonic (n+1) : ℝ)⌋ < ⌊Real.exp (harmonic n : ℝ)⌋ + 3 := by
    exact_mod_cast hcast
  omega

theorem part1 (n : ℕ) (hn : 1 ≤ n) : A206911_diff n ∈ ({2,3} : Set ℤ) := by
  rw [diff_eq]
  have hge := increment_ge n
  have hle := increment_le n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega
theorem ff_one : ff 1 = 2 := by
  rw [ff]
  have hh : (harmonic 1 : ℝ) = 1 := by norm_num [harmonic, Finset.sum_range_succ]
  rw [hh, Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · push_cast; linarith [Real.exp_one_gt_d9]
  · push_cast; linarith [Real.exp_one_lt_d9]

theorem indicator_eq (n : ℕ) :
    ((if A206911_diff (n+1) = 3 then 1 else 0 : ℤ)) = ff (n+2) - ff (n+1) - 1 := by
  have hd : A206911_diff (n+1) = 1 + ff (n+2) - ff (n+1) := diff_eq (n+1)
  have hmem := part1 (n+1) (by omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  split_ifs with hcond <;> omega

theorem count_threes_eq (N : ℕ) : (count_threes N : ℤ) = ff (N+1) - 2 - N := by
  have hstep : (count_threes N : ℤ) = ∑ n ∈ range N, (ff (n+2) - ff (n+1) - 1) := by
    rw [count_threes, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← indicator_eq n]
    simp
  rw [hstep, Finset.sum_sub_distrib]
  have htel : ∑ n ∈ range N, (ff (n+2) - ff (n+1)) = ff (N+1) - ff 1 := by
    have := Finset.sum_range_sub (fun n => ff (n+1)) N
    simpa using this
  rw [htel, Finset.sum_const, Finset.card_range, ff_one]
  ring

theorem count_threes_le (N : ℕ) : count_threes N ≤ N := by
  rw [count_threes]
  calc (range N).sum (fun n => if A206911_diff (n + 1) = 3 then 1 else 0)
      ≤ (range N).sum (fun _ => 1) := by
        apply Finset.sum_le_sum; intro n _; split_ifs <;> simp
    _ = N := by simp

theorem count_twos_eq (N : ℕ) : (count_twos N : ℤ) = 2*N + 2 - ff (N+1) := by
  rw [count_twos, Nat.cast_sub (count_threes_le N), count_threes_eq]
  ring

/-- `ff(N+1)/(N+1) → E`. -/
theorem tendsto_w :
    Tendsto (fun N : ℕ => (ff (N+1) : ℝ) / ((N:ℝ)+1)) atTop (𝓝 E) := by
  have hexp : Tendsto (fun N : ℕ => Real.exp ((harmonic N : ℝ) - Real.log N)) atTop (𝓝 E) := by
    have hc := (Real.continuous_exp.tendsto Real.eulerMascheroniConstant).comp
      Real.tendsto_harmonic_sub_log
    simpa [E, Function.comp] using hc
  have hexpS : Tendsto (fun N : ℕ => Real.exp ((harmonic (N+1) : ℝ) - Real.log ((N:ℝ)+1)))
      atTop (𝓝 E) := by
    have h := hexp.comp (tendsto_add_atTop_nat 1)
    refine h.congr ?_
    intro N
    simp only [Function.comp]
    norm_num
  have hE1 : Tendsto (fun N : ℕ => Real.exp (harmonic (N+1) : ℝ) / ((N:ℝ)+1)) atTop (𝓝 E) := by
    refine hexpS.congr ?_
    intro N
    rw [Real.exp_sub, Real.exp_log (by positivity)]
  have h0 : Tendsto (fun N : ℕ => (1:ℝ) / ((N:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Tendsto (fun N : ℕ => (Real.exp (harmonic (N+1) : ℝ) - 1) / ((N:ℝ)+1))
      atTop (𝓝 E) := by
    have hsub := hE1.sub h0
    rw [sub_zero] at hsub
    refine hsub.congr ?_
    intro N
    rw [sub_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hE1 ?_ ?_
  · filter_upwards with N
    have hlt : Real.exp (harmonic (N+1) : ℝ) - 1 ≤ (ff (N+1) : ℝ) := by
      rw [ff]; exact (Int.sub_one_lt_floor _).le
    gcongr
  · filter_upwards with N
    have hle : (ff (N+1) : ℝ) ≤ Real.exp (harmonic (N+1) : ℝ) := by
      rw [ff]; exact Int.floor_le _
    gcongr

/-- The limiting ratio. -/
noncomputable def limitRatio : ℝ := (E - 1) / (2 - E)

theorem part2 :
    ∃ l : ℝ, 3.5 < l ∧ l < 3.6 ∧
      Tendsto ratio_threes_to_twos atTop (𝓝 l) := by
  have hElt : E < 41/23 := E_lt
  have hEgt : (16:ℝ)/9 < E := E_gt
  have h2E : (0:ℝ) < 2 - E := by linarith
  -- casts of counts
  have hct : ∀ N : ℕ, (count_threes N : ℝ) = (ff (N+1):ℝ) - 2 - (N:ℝ) := by
    intro N
    have h := count_threes_eq N
    have e : (count_threes N : ℝ) = ((count_threes N : ℤ) : ℝ) := by push_cast; ring
    rw [e, h]; push_cast; ring
  have hct2 : ∀ N : ℕ, (count_twos N : ℝ) = 2*(N:ℝ) + 2 - (ff (N+1):ℝ) := by
    intro N
    have h := count_twos_eq N
    have e : (count_twos N : ℝ) = ((count_twos N : ℤ) : ℝ) := by push_cast; ring
    rw [e, h]; push_cast; ring
  -- limits of num/(N+1) and den/(N+1)
  have hc1 : Tendsto (fun N : ℕ => (2+(N:ℝ))/((N:ℝ)+1)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun N : ℕ => (1:ℝ) / ((N:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop (α:=ℕ))).add h0
    rw [add_zero] at this
    refine this.congr ?_
    intro N
    have : ((N:ℝ)+1) ≠ 0 := by positivity
    field_simp
    ring
  have hnum : Tendsto (fun N : ℕ => (count_threes N:ℝ)/((N:ℝ)+1)) atTop (𝓝 (E-1)) := by
    have hsub := tendsto_w.sub hc1
    refine hsub.congr ?_
    intro N
    rw [hct N]
    have hne : ((N:ℝ)+1) ≠ 0 := by positivity
    field_simp
    ring
  have hden : Tendsto (fun N : ℕ => (count_twos N:ℝ)/((N:ℝ)+1)) atTop (𝓝 (2-E)) := by
    have hconst : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have hsub := hconst.sub tendsto_w
    refine hsub.congr ?_
    intro N
    rw [hct2 N]
    have hne : ((N:ℝ)+1) ≠ 0 := by positivity
    field_simp
  -- eventually count_twos ≠ 0
  have hev : ∀ᶠ N : ℕ in atTop, count_twos N ≠ 0 := by
    have hpos := hden.eventually (eventually_gt_nhds h2E)
    filter_upwards [hpos] with N hN
    intro hzero
    rw [hzero] at hN
    simp at hN
  -- q → limitRatio
  have hq : Tendsto (fun N : ℕ => ((count_threes N:ℝ)/((N:ℝ)+1)) / ((count_twos N:ℝ)/((N:ℝ)+1)))
      atTop (𝓝 limitRatio) := by
    rw [limitRatio]
    exact hnum.div hden (by linarith)
  -- ratio =ᶠ q
  refine ⟨limitRatio, ?_, ?_, ?_⟩
  · -- 3.5 < limitRatio
    rw [limitRatio, lt_div_iff₀ h2E]
    nlinarith [hEgt]
  · rw [limitRatio, div_lt_iff₀ h2E]
    nlinarith [hElt]
  · refine hq.congr' ?_
    filter_upwards [hev] with N hN
    rw [ratio_threes_to_twos, if_neg hN]
    have hne : ((N:ℝ)+1) ≠ 0 := by positivity
    have hne2 : (count_twos N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp

/--
Conjecture: the difference sequence of A206911 consists of 2s and 3s,
and the ratio (number of 3s)/(number of 2s) tends to a number between 3.5 and 3.6.
-/
theorem oeis_a206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n ∈ ({2, 3} : Set ℤ)) ∧
  (∃ l : ℝ,
    3.5 < l ∧ l < 3.6 ∧
    Tendsto ratio_threes_to_twos atTop (nhds l)) := by
  exact ⟨fun n hn => part1 n hn, part2⟩
