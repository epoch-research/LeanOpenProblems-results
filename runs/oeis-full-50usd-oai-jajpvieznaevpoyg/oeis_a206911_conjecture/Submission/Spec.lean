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


namespace A206911_Work
open Real Finset Filter

noncomputable def S (n : ℕ) : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

lemma S_eq_harmonic (n : ℕ) : S n = (harmonic n : ℚ) := by
  rw [S, harmonic]
  simp [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma exp_S_pos (n : ℕ) : 0 < exp (S n) := exp_pos _

lemma log_two_mul_self_gt_H5 : S 5 < Real.log (2 * (5:ℝ)) := by
  rw [S_eq_harmonic]
  norm_num [harmonic]
  -- H_5 = 137/60, prove exp(137/60)<10
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10)).2 (show Real.exp (137/60 : ℝ) < 10 by
    have hsmall : Real.exp (17/60 : ℝ) < 4/3 := by
      have h := Real.exp_bound' (x := (17/60 : ℝ)) (n := 5)
        (by norm_num) (by norm_num) (by norm_num)
      refine lt_of_le_of_lt h ?_
      rw [show 5 = 1+1+1+1+1 from rfl]
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    calc
      Real.exp (137/60 : ℝ) = Real.exp (2 + 17/60) := by norm_num
      _ = Real.exp 2 * Real.exp (17/60 : ℝ) := by rw [Real.exp_add]
      _ = Real.exp 1 ^ (2:ℕ) * Real.exp (17/60 : ℝ) := by
        rw [show (2:ℝ)=1+1 by norm_num, Real.exp_add]
        ring
      _ < (2.7182818286:ℝ)^2 * (4/3) := by gcongr; exact Real.exp_one_lt_d9
      _ < 10 := by norm_num)

lemma S_lt_log_two_mul (n : ℕ) (hn : 5 ≤ n) : S n < Real.log (2 * (n:ℝ)) := by
  induction' hn with n hn ih
  · exact log_two_mul_self_gt_H5
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hn)
    have hstep : (1 / ((n : ℝ) + 1)) ≤ Real.log (1 + 1 / (n : ℝ)) := by
      have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / (n:ℝ) by positivity)
      have heq : 1 - (1 + 1 / (n:ℝ))⁻¹ = 1 / ((n:ℝ)+1) := by
        field_simp [show (n:ℝ) ≠ 0 by positivity]
        ring
      rw [← heq]
      exact h
    rw [S, Finset.sum_range_succ, ← S]
    calc
      S n + 1 / ((n : ℝ) + 1) < Real.log (2 * (n:ℝ)) + Real.log (1 + 1 / (n:ℝ)) := by linarith
      _ = Real.log (2 * ((n:ℝ)+1)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp [show (n:ℝ) ≠ 0 by positivity]
      _ = Real.log (2 * ((n+1:ℕ):ℝ)) := by rw [Nat.cast_add_one]

lemma exp_S_lt_two_n (n : ℕ) (hn : 5 ≤ n) : exp (S n) < 2 * (n:ℝ) := by
  have h := S_lt_log_two_mul n hn
  have hpos : 0 < 2 * (n:ℝ) := by positivity
  rwa [Real.lt_log_iff_exp_lt hpos] at h


lemma S_nonneg (n : ℕ) : 0 ≤ S n := by
  rw [S]
  exact Finset.sum_nonneg fun k hk => by positivity

lemma exp_S_sub_one_nonneg (n : ℕ) : 0 ≤ exp (S n) - 1 := by
  exact sub_nonneg.mpr (Real.one_le_exp (S_nonneg n))

lemma A206911_int_eq (n : ℕ) : (A206911 n : ℤ) = (n : ℤ) + (⌊exp (S n) - 1⌋₊ : ℕ) := by
  unfold A206911 S
  simp

lemma log_add_one_le_S (n : ℕ) : Real.log ((n:ℝ)+1) ≤ S n := by
  rw [S_eq_harmonic]
  simpa [Nat.cast_add_one] using (log_add_one_le_harmonic n)

lemma exp_S_ge_np1 (n : ℕ) : (n:ℝ)+1 ≤ exp (S n) := by
  have h := log_add_one_le_S n
  have hpos : 0 < (n:ℝ)+1 := by positivity
  rwa [Real.log_le_iff_le_exp hpos] at h

lemma exp_step_sub_bounds (n : ℕ) (hn : 5 ≤ n) :
    1 < exp (S (n+1)) - exp (S n) ∧ exp (S (n+1)) - exp (S n) < 2 := by
  have hnposN : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast hnposN
  have hs : S (n+1) = S n + 1 / ((n:ℝ)+1) := by
    rw [S, Finset.sum_range_succ, ← S]
  rw [hs, Real.exp_add]
  have htpos : 0 < 1 / ((n:ℝ)+1) := by positivity
  have htexp_lower : 1 + 1 / ((n:ℝ)+1) < exp (1 / ((n:ℝ)+1)) := by
    simpa [add_comm] using Real.add_one_lt_exp (x := 1 / ((n:ℝ)+1)) (by positivity)
  have hlower : 1 < exp (S n) * (exp (1 / ((n:ℝ)+1)) - 1) := by
    have hA := exp_S_ge_np1 n
    have hB : 1 / ((n:ℝ)+1) < exp (1 / ((n:ℝ)+1)) - 1 := by linarith
    calc
      1 = ((n:ℝ)+1) * (1 / ((n:ℝ)+1)) := by field_simp
      _ ≤ exp (S n) * (1 / ((n:ℝ)+1)) := by gcongr
      _ < exp (S n) * (exp (1 / ((n:ℝ)+1)) - 1) := by gcongr
  have hupper : exp (S n) * (exp (1 / ((n:ℝ)+1)) - 1) < 2 := by
    have hES := exp_S_lt_two_n n hn
    have htlt : 1 / ((n:ℝ)+1) < 1 := by
      rw [div_lt_one₀ (by positivity : (0:ℝ)<(n:ℝ)+1)]
      nlinarith
    have hEB := Real.exp_bound_div_one_sub_of_interval' htpos htlt
    have hB : exp (1 / ((n:ℝ)+1)) - 1 < 1 / (n:ℝ) := by
      have htmp : exp (1 / ((n:ℝ)+1)) < ((n:ℝ)+1) / (n:ℝ) := by
        calc
          exp (1 / ((n:ℝ)+1)) < 1 / (1 - 1 / ((n:ℝ)+1)) := hEB
          _ = ((n:ℝ)+1) / (n:ℝ) := by
            field_simp [show (n:ℝ) ≠ 0 by positivity]
            ring
      calc
        exp (1 / ((n:ℝ)+1)) - 1 < ((n:ℝ)+1) / (n:ℝ) - 1 := by linarith
        _ = 1 / (n:ℝ) := by
          field_simp [show (n:ℝ) ≠ 0 by positivity]
          ring
    have hBnonneg : 0 ≤ exp (1 / ((n:ℝ)+1)) - 1 := by
      exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
    calc
      exp (S n) * (exp (1 / ((n:ℝ)+1)) - 1) < (2*(n:ℝ)) * (1/(n:ℝ)) := by gcongr
      _ = 2 := by field_simp [show (n:ℝ) ≠ 0 by positivity]
  constructor <;> nlinarith

lemma floor_increment_one_or_two {y d : ℝ} (hy0 : 0 ≤ y) (hd1 : 1 < d) (hd2 : d < 2) :
    ((⌊y + d⌋₊ : ℕ) : ℤ) - ((⌊y⌋₊ : ℕ) : ℤ) = (1:ℤ) ∨
      ((⌊y + d⌋₊ : ℕ) : ℤ) - ((⌊y⌋₊ : ℕ) : ℤ) = (2:ℤ) := by
  have hyd0 : 0 ≤ y + d := by linarith
  have hge_nat : ⌊y⌋₊ + 1 ≤ ⌊y + d⌋₊ := by
    apply Nat.le_floor
    have hy : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
    norm_num
    linarith
  have hlt_nat : ⌊y + d⌋₊ < ⌊y⌋₊ + 3 := by
    rw [Nat.floor_lt hyd0]
    have hy : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    norm_num
    linarith
  omega

lemma A206911_diff_large (n : ℕ) (hn : 5 ≤ n) : A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  have hb := exp_step_sub_bounds n hn
  have hfloor := floor_increment_one_or_two (y := exp (S n) - 1)
    (d := exp (S (n+1)) - exp (S n)) (exp_S_sub_one_nonneg n) hb.1 hb.2
  have hy : exp (S n) - 1 + (exp (S (n+1)) - exp (S n)) = exp (S (n+1)) - 1 := by ring
  rw [hy] at hfloor
  rw [A206911_diff, A206911_int_eq, A206911_int_eq]
  norm_num at hfloor ⊢
  rcases hfloor with hf | hf
  · left; omega
  · right; omega



/-- Auxiliary sharp bounds for Euler-Mascheroni constant. -/
noncomputable def corrLow (n : ℕ) : ℝ := (harmonic n : ℚ) - Real.log n - 1 / (2 * n)
noncomputable def corrHigh (n : ℕ) : ℝ := if n=0 then 100 else corrLow n + 1/(12*n^2)

lemma atanh_upper_alg {t : ℝ} (ht : 0 < t) :
    2 * ((1 / (2*t+1)) + (1 / (2*t+1))^3 / (1 - (1/(2*t+1))^2)) =
    (2*t+1)/(2*t*(t+1)) := by
  have h1 : 2*t+1 ≠ 0 := by positivity
  have h2 : t ≠ 0 := by positivity
  have h3 : t+1 ≠ 0 := by positivity
  have hx0 : 0 < 1/(2*t+1) := by positivity
  have hx1 : 1/(2*t+1) < 1 := by
    rw [div_lt_one₀ (by positivity : 0 < 2*t+1)]
    linarith
  have h4 : 1 - (1/(2*t+1))^2 ≠ 0 := by
    have hxabs : |1/(2*t+1)| < |(1:ℝ)| := by rw [abs_of_pos hx0, abs_one]; exact hx1
    have hx2 : (1/(2*t+1))^2 < 1 := by simpa using (sq_lt_sq.mpr hxabs)
    nlinarith
  field_simp [h1,h2,h3,h4]
  have hden : (2 * t + 1) ^ 2 - 1 ≠ 0 := by nlinarith [mul_pos ht (by linarith : 0 < t+1)]
  field_simp [hden]
  ring

lemma atanh_lower_alg {t : ℝ} (ht : 0 < t) :
    (2*t+1)/(2*t*(t+1)) + (1/(12*(t+1)^2) - 1/(12*t^2)) <
    2 * ((1 / (2*t+1)) + (1/3) * (1 / (2*t+1))^3) := by
  have h1 : 2*t+1 ≠ 0 := by positivity
  have h2 : t ≠ 0 := by positivity
  have h3 : t+1 ≠ 0 := by positivity
  field_simp [h1,h2,h3]
  ring_nf
  nlinarith [sq_nonneg t, ht]

lemma log_one_add_inv_bounds (n : ℕ) (hn : 0 < n) :
    (2 * ((1 / (2*(n:ℝ)+1)) + (1/3) * (1 / (2*(n:ℝ)+1))^3)) < Real.log (1+1/(n:ℝ)) ∧
    Real.log (1+1/(n:ℝ)) ≤ 2 * ((1 / (2*(n:ℝ)+1)) + (1 / (2*(n:ℝ)+1))^3 / (1 - (1/(2*(n:ℝ)+1))^2)) := by
  let x : ℝ := 1/(2*(n:ℝ)+1)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hx0 : 0 ≤ x := by positivity
  have hxpos : 0 < x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one₀ (by positivity : (0:ℝ)<2*(n:ℝ)+1)]
    nlinarith
  have hratio : (1+x)/(1-x)=1+1/(n:ℝ) := by
    dsimp [x]
    field_simp [show (n:ℝ) ≠ 0 by positivity, show 2*(n:ℝ)+1 ≠ 0 by positivity]
    ring
  constructor
  · have h3 := Real.sum_range_le_log_div (x:=x) hx0 hx1 3
    rw [show (3:ℕ)=2+1 by norm_num, Finset.sum_range_succ] at h3
    rw [show (2:ℕ)=1+1 by norm_num, Finset.sum_range_succ] at h3
    rw [Finset.sum_range_one] at h3
    have hpos5 : 0 < x ^ 5 / 5 := by positivity
    have hstrict : x + x^3/3 < 1/2 * Real.log ((1+x)/(1-x)) := by
      norm_num at h3 ⊢
      nlinarith
    rw [hratio] at hstrict
    nlinarith
  · have hu := Real.log_div_le_sum_range_add (x:=x) hx0 hx1 1
    rw [Finset.sum_range_one] at hu
    rw [hratio] at hu
    change Real.log (1 + 1 / (n : ℝ)) ≤ 2 * (x + x ^ 3 / (1 - x ^ 2))
    nlinarith

lemma corrLow_step (m:ℕ) : corrLow m ≤ corrLow (m+1) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · norm_num [corrLow, harmonic_zero, harmonic_succ]
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hb := (log_one_add_inv_bounds m hm).2
  have hcalc : Real.log (1+1/(m:ℝ)) ≤ (2*(m:ℝ)+1)/(2*(m:ℝ)*((m:ℝ)+1)) := by
    rw [atanh_upper_alg hmR] at hb
    exact hb
  rw [corrLow, corrLow, harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
  have hlog : Real.log (m+1:ℝ)=Real.log (m:ℝ)+Real.log (1+1/(m:ℝ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp [show (m:ℝ)≠0 by positivity]
  rw [Nat.cast_add_one, hlog]
  have hdiff : (↑(harmonic m) + (((m:ℝ)+1)⁻¹) - (Real.log ↑m + Real.log (1 + 1 / ↑m)) - 1 / (2 * ((m:ℝ)+1))) - (↑(harmonic m) - Real.log ↑m - 1 / (2 * ↑m)) = (2*(m:ℝ)+1)/(2*(m:ℝ)*((m:ℝ)+1)) - Real.log (1+1/(m:ℝ)) := by
    field_simp [show (m:ℝ)≠0 by positivity, show (m:ℝ)+1≠0 by positivity]
    ring
  apply sub_nonneg.mp
  rw [hdiff]
  linarith

lemma corrHigh_step (m:ℕ) : corrHigh (m+1) ≤ corrHigh m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · norm_num [corrHigh, corrLow, harmonic_zero, harmonic_succ]
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hb := (log_one_add_inv_bounds m hm).1
  have hcalc : (2*(m:ℝ)+1)/(2*(m:ℝ)*((m:ℝ)+1)) + (1/(12*((m:ℝ)+1)^2)-1/(12*(m:ℝ)^2)) < Real.log (1+1/(m:ℝ)) := by
    exact lt_trans (atanh_lower_alg hmR) hb
  rw [corrHigh, corrHigh, corrLow, corrLow, harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
  simp [hm.ne', Nat.succ_ne_zero]
  have hlog : Real.log (m+1:ℝ)=Real.log (m:ℝ)+Real.log (1+1/(m:ℝ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp [show (m:ℝ)≠0 by positivity]
  rw [hlog]
  have hdiff : (↑(harmonic m) - Real.log ↑m - 1 / (2 * ↑m) + 1 / (12 * ↑m ^ 2)) - (↑(harmonic m) + (((m:ℝ)+1)⁻¹) - (Real.log ↑m + Real.log (1 + 1 / ↑m)) - 1 / (2 * ((m:ℝ)+1)) + 1 / (12 * (((m:ℝ)+1)^2))) = Real.log (1+1/(m:ℝ)) - ((2*(m:ℝ)+1)/(2*(m:ℝ)*((m:ℝ)+1)) + (1/(12*((m:ℝ)+1)^2)-1/(12*(m:ℝ)^2))) := by
    field_simp [show (m:ℝ)≠0 by positivity, show (m:ℝ)+1≠0 by positivity]
    ring
  apply sub_nonneg.mp
  have hnon : 0 ≤ Real.log (1+1/(m:ℝ)) - ((2*(m:ℝ)+1)/(2*(m:ℝ)*((m:ℝ)+1)) + (1/(12*((m:ℝ)+1)^2)-1/(12*(m:ℝ)^2))) := by linarith
  convert hnon using 1
  field_simp [show (m:ℝ)≠0 by positivity, show (m:ℝ)+1≠0 by positivity]
  ring

open Filter
lemma corrLow_mono : Monotone corrLow := monotone_nat_of_le_succ corrLow_step
lemma corrHigh_antitone : Antitone corrHigh := antitone_nat_of_succ_le corrHigh_step

lemma tendsto_corrLow : Tendsto corrLow atTop (nhds Real.eulerMascheroniConstant) := by
  have hzero : Tendsto (fun n : ℕ => (1 / (2 : ℝ)) * (1 / (n : ℝ))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1 / (2 : ℝ)) * (1 / (n : ℝ))) atTop (nhds ((1/(2:ℝ))*0)))
  have hcorr := Real.tendsto_harmonic_sub_log.sub hzero
  have hcongr : (fun n : ℕ => (harmonic n : ℝ) - Real.log n - (1 / (2 : ℝ)) * (1 / (n : ℝ))) =ᶠ[atTop] corrLow := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [corrLow]
    field_simp [show (n:ℝ)≠0 by exact_mod_cast hn]
  simpa using hcorr.congr' hcongr

lemma tendsto_corrHigh : Tendsto corrHigh atTop (nhds Real.eulerMascheroniConstant) := by
  have hone : Tendsto (fun n : ℕ => (1 / (n : ℝ))) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hzero : Tendsto (fun n : ℕ => (1 / (12 : ℝ)) * ((1 / (n : ℝ)) * (1 / (n : ℝ)))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hone.mul hone) : Tendsto (fun n : ℕ => (1/(12:ℝ))*((1/(n:ℝ))*(1/(n:ℝ)))) atTop (nhds ((1/(12:ℝ))*(0*0))))
  have h := tendsto_corrLow.add hzero
  have hcongr : (fun n : ℕ => corrLow n + (1 / (12 : ℝ)) * ((1 / (n : ℝ)) * (1 / (n : ℝ)))) =ᶠ[atTop] corrHigh := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [corrHigh, if_neg hn]
    field_simp [show (n:ℝ)≠0 by exact_mod_cast hn]
  simpa using h.congr' hcongr

lemma gamma_between_corr7 : corrLow 7 ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ corrHigh 7 := by
  exact ⟨(corrLow_mono.ge_of_tendsto tendsto_corrLow 7), (corrHigh_antitone.le_of_tendsto tendsto_corrHigh 7)⟩

lemma exp_353_140_gt : (112/9 : ℝ) < Real.exp (353/140 : ℝ) := by
  have hsmall : (112/9 : ℝ) < (2.7182818283:ℝ)^2 * (∑ k ∈ Finset.range 6, (73/140:ℝ)^k / k.factorial) := by
    rw [show 6 = 1+1+1+1+1+1 from rfl]
    repeat rw [Finset.sum_range_succ]
    norm_num [Nat.factorial]
  calc
    (112/9 : ℝ) < (2.7182818283:ℝ)^2 * (∑ k ∈ Finset.range 6, (73/140:ℝ)^k / k.factorial) := hsmall
    _ ≤ (Real.exp 1)^2 * Real.exp (73/140 : ℝ) := by
      have hpow : (2.7182818283:ℝ)^2 ≤ (Real.exp 1)^2 := by
        exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 2
      have hsum : (∑ k ∈ Finset.range 6, (73/140:ℝ)^k / k.factorial) ≤ Real.exp (73/140 : ℝ) :=
        Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 73/140) 6
      exact mul_le_mul hpow hsum (by positivity) (by positivity)
    _ = Real.exp (353/140 : ℝ) := by
      rw [show (353/140:ℝ)=1+1+73/140 by norm_num, Real.exp_add, Real.exp_add]
      ring

lemma exp_3709_1470_lt : Real.exp (3709/1470 : ℝ) < (287/23 : ℝ) := by
  have hsmall : (2.7182818286:ℝ)^2 * ((∑ k ∈ Finset.range 4, (769/1470:ℝ)^k / k.factorial) + (769/1470:ℝ)^4 * (5:ℝ) / (Nat.factorial 4 * 4)) < (287/23 : ℝ) := by
    repeat rw [Finset.sum_range_succ]
    norm_num [Nat.factorial]
  calc
    Real.exp (3709/1470 : ℝ) = (Real.exp 1)^2 * Real.exp (769/1470 : ℝ) := by
      rw [show (3709/1470:ℝ)=1+1+769/1470 by norm_num, Real.exp_add, Real.exp_add]
      ring
    _ ≤ (2.7182818286:ℝ)^2 * ((∑ k ∈ Finset.range 4, (769/1470:ℝ)^k / k.factorial) + (769/1470:ℝ)^4 * (5:ℝ) / (Nat.factorial 4 * 4)) := by
      have hpow : (Real.exp 1)^2 ≤ (2.7182818286:ℝ)^2 := by
        exact pow_le_pow_left₀ (by positivity) Real.exp_one_lt_d9.le 2
      have hsum : Real.exp (769/1470 : ℝ) ≤ (∑ k ∈ Finset.range 4, (769/1470:ℝ)^k / k.factorial) + (769/1470:ℝ)^4 * (5:ℝ) / (Nat.factorial 4 * 4) := by
        have htmp := Real.exp_bound' (x := (769/1470:ℝ)) (n := 4) (by norm_num) (by norm_num) (by norm_num)
        norm_num at htmp ⊢
        exact htmp
      exact mul_le_mul hpow hsum (by positivity) (by positivity)
    _ < (287/23 : ℝ) := hsmall

lemma exp_gamma_bounds : (16/9 : ℝ) < Real.exp Real.eulerMascheroniConstant ∧ Real.exp Real.eulerMascheroniConstant < (41/23 : ℝ) := by
  have hb := gamma_between_corr7
  constructor
  · have hlow : (16/9 : ℝ) < Real.exp (corrLow 7) := by
      have hc : corrLow 7 = ((363/140 : ℝ) - Real.log 7) - 1/14 := by
        rw [corrLow]
        norm_num [harmonic]
      rw [hc]
      have heq : Real.exp (((363/140 : ℝ) - Real.log 7) - 1/14) = Real.exp (353/140 : ℝ) / 7 := by
        rw [Real.exp_sub ((363/140 : ℝ) - Real.log 7) (1/14)]
        rw [Real.exp_sub (363/140 : ℝ) (Real.log 7)]
        rw [Real.exp_log (by norm_num : (0:ℝ)<7)]
        field_simp [Real.exp_ne_zero]
        rw [← Real.exp_add]
        norm_num
      rw [heq]
      nlinarith [exp_353_140_gt]
    exact hlow.trans_le (Real.exp_le_exp.mpr hb.1)
  · have hhigh : Real.exp (corrHigh 7) < (41/23 : ℝ) := by
      have hc : corrHigh 7 = (363/140 : ℝ) - Real.log 7 - 1/14 + 1/588 := by
        rw [corrHigh]
        norm_num [corrLow, harmonic]
      rw [hc]
      have heq : Real.exp ((363/140 : ℝ) - Real.log 7 - 1/14 + 1/588) = Real.exp (3709/1470 : ℝ) / 7 := by
        rw [show (363/140 : ℝ) - Real.log 7 - 1/14 + 1/588 = (3709/1470 : ℝ) - Real.log 7 by ring]
        rw [Real.exp_sub (3709/1470 : ℝ) (Real.log 7)]
        rw [Real.exp_log (by norm_num : (0:ℝ)<7)]
      rw [heq]
      nlinarith [exp_3709_1470_lt]
    exact (Real.exp_le_exp.mpr hb.2).trans_lt hhigh

/-- Finite exponential floor computations for the initial values. -/

lemma exp_half_lt_five_thirds : Real.exp (1/2:ℝ) < 5/3 := by
  have h := Real.exp_bound' (x := (1/2:ℝ)) (n:=4) (by norm_num) (by norm_num) (by norm_num)
  refine lt_of_le_of_lt h ?_
  repeat rw [Finset.sum_range_succ]
  norm_num [Nat.factorial]

lemma floor_exp_three_halves : ⌊Real.exp (3/2:ℝ)⌋₊ = 4 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ Real.exp (3/2:ℝ))]
  constructor
  · have h : (4:ℝ) < ∑ k ∈ Finset.range 4, (3/2:ℝ)^k / k.factorial := by
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    exact le_of_lt (lt_of_lt_of_le h (Real.sum_le_exp_of_nonneg (by norm_num) 4))
  · calc
      Real.exp (3/2:ℝ) = Real.exp 1 * Real.exp (1/2:ℝ) := by rw [show (3/2:ℝ)=1+1/2 by norm_num, Real.exp_add]
      _ < 2.7182818286 * (5/3:ℝ) := by exact mul_lt_mul Real.exp_one_lt_d9 exp_half_lt_five_thirds.le (by positivity) (by positivity)
      _ < (4:ℝ)+1 := by norm_num

lemma exp_five_six_lt_two : Real.exp (5/6:ℝ) < 5/2 := by
  have h := Real.exp_bound' (x := (5/6:ℝ)) (n:=6) (by norm_num) (by norm_num) (by norm_num)
  refine lt_of_le_of_lt h ?_
  repeat rw [Finset.sum_range_succ]
  norm_num [Nat.factorial]

lemma floor_exp_eleven_sixths : ⌊Real.exp (11/6:ℝ)⌋₊ = 6 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ Real.exp (11/6:ℝ))]
  constructor
  · have h : (6:ℝ) < ∑ k ∈ Finset.range 5, (11/6:ℝ)^k / k.factorial := by
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    exact le_of_lt (lt_of_lt_of_le h (Real.sum_le_exp_of_nonneg (by norm_num) 5))
  · calc
      Real.exp (11/6:ℝ) = Real.exp 1 * Real.exp (5/6:ℝ) := by rw [show (11/6:ℝ)=1+5/6 by norm_num, Real.exp_add]
      _ < 2.7182818286 * (5/2:ℝ) := by exact mul_lt_mul Real.exp_one_lt_d9 exp_five_six_lt_two.le (by positivity) (by positivity)
      _ < (6:ℝ)+1 := by norm_num

lemma floor_exp_twentyfive_twelfths : ⌊Real.exp (25/12:ℝ)⌋₊ = 8 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ Real.exp (25/12:ℝ))]
  constructor
  · have h : (8:ℝ) < ∑ k ∈ Finset.range 8, (25/12:ℝ)^k / k.factorial := by
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    exact le_of_lt (lt_of_lt_of_le h (Real.sum_le_exp_of_nonneg (by norm_num) 8))
  · have hsmall : Real.exp (1/12:ℝ) < 11/10 := by
      have h := Real.exp_bound' (x := (1/12:ℝ)) (n:=3) (by norm_num) (by norm_num) (by norm_num)
      refine lt_of_le_of_lt h ?_
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    calc
      Real.exp (25/12:ℝ) = (Real.exp 1)^2 * Real.exp (1/12:ℝ) := by
        rw [show (25/12:ℝ)=1+1+1/12 by norm_num, Real.exp_add, Real.exp_add]
        ring
      _ < (2.7182818286:ℝ)^2 * (11/10:ℝ) := by gcongr <;> (first | exact Real.exp_one_lt_d9 | exact hsmall)
      _ < (8:ℝ)+1 := by norm_num

lemma floor_exp_137_60 : ⌊Real.exp (137/60:ℝ)⌋₊ = 9 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ Real.exp (137/60:ℝ))]
  constructor
  · have h : (9:ℝ) < ∑ k ∈ Finset.range 5, (137/60:ℝ)^k / k.factorial := by
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    exact le_of_lt (lt_of_lt_of_le h (Real.sum_le_exp_of_nonneg (by norm_num) 5))
  · -- reuse existing style: exp(137/60)<10
    have hsmall : Real.exp (17/60 : ℝ) < 4/3 := by
      have h := Real.exp_bound' (x := (17/60 : ℝ)) (n := 5) (by norm_num) (by norm_num) (by norm_num)
      refine lt_of_le_of_lt h ?_
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    calc
      Real.exp (137/60 : ℝ) = Real.exp 1 ^ (2:ℕ) * Real.exp (17/60 : ℝ) := by
        rw [show (137/60:ℝ)=1+1+17/60 by norm_num, Real.exp_add, Real.exp_add]
        ring
      _ < (2.7182818286:ℝ)^2 * (4/3) := by gcongr; exact Real.exp_one_lt_d9
      _ < (9:ℝ)+1 := by norm_num


end A206911_Work


namespace A206911_Work

lemma floor_exp_one_nat : ⌊Real.exp (1:ℝ)⌋₊ = 2 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ Real.exp (1:ℝ))]
  constructor
  · exact Real.exp_one_gt_two.le
  · norm_num
    exact Real.exp_one_lt_three

lemma A206911_val_one : (A206911 1 : ℤ) = 2 := by
  rw [A206911_int_eq]
  rw [S]
  norm_num [floor_exp_one_nat, Nat.floor_sub_one]

lemma A206911_val_two : (A206911 2 : ℤ) = 5 := by
  rw [A206911_int_eq]
  rw [S]
  norm_num [floor_exp_three_halves, Nat.floor_sub_one]

lemma A206911_val_three : (A206911 3 : ℤ) = 8 := by
  rw [A206911_int_eq]
  rw [S]
  norm_num [floor_exp_eleven_sixths, Nat.floor_sub_one]

lemma A206911_val_four : (A206911 4 : ℤ) = 11 := by
  rw [A206911_int_eq]
  rw [S]
  norm_num [floor_exp_twentyfive_twelfths, Nat.floor_sub_one]

lemma A206911_val_five : (A206911 5 : ℤ) = 13 := by
  rw [A206911_int_eq]
  rw [S]
  norm_num [floor_exp_137_60, Nat.floor_sub_one]

lemma A206911_diff_small (n : ℕ) (hn1 : 1 ≤ n) (hn5 : n < 5) :
    A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  interval_cases n <;> simp [A206911_diff, A206911_val_one, A206911_val_two,
    A206911_val_three, A206911_val_four, A206911_val_five]

lemma A206911_diff_all (n : ℕ) (hn : 1 ≤ n) : A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  by_cases h : n < 5
  · exact A206911_diff_small n hn h
  · exact A206911_diff_large n (by omega)

end A206911_Work


namespace A206911_Work
open Real Finset Filter

noncomputable def F (n : ℕ) : ℕ := ⌊Real.exp (S n) - 1⌋₊

lemma A206911_int_eq_F (n : ℕ) : (A206911 n : ℤ) = (n : ℤ) + (F n : ℕ) := by
  simpa [F] using A206911_int_eq n

lemma tendsto_S_sub_log :
    Tendsto (fun n : ℕ => S n - Real.log (n : ℝ)) atTop (nhds Real.eulerMascheroniConstant) := by
  have hfun : (fun n : ℕ => S n - Real.log (n : ℝ)) =
      (fun n : ℕ => (harmonic n : ℝ) - Real.log (n : ℝ)) := by
    funext n
    rw [S_eq_harmonic]
  simpa [hfun] using Real.tendsto_harmonic_sub_log

lemma tendsto_exp_S_div :
    Tendsto (fun n : ℕ => Real.exp (S n) / (n : ℝ)) atTop
      (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have h := tendsto_S_sub_log.rexp
  have hcongr : (fun n : ℕ => Real.exp (S n - Real.log (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => Real.exp (S n) / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.exp_sub, Real.exp_log hnpos]
  exact h.congr' hcongr

lemma tendsto_F_div :
    Tendsto (fun n : ℕ => (F n : ℝ) / (n : ℝ)) atTop
      (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have herr : Tendsto (fun n : ℕ => ((F n : ℝ) - Real.exp (S n)) / (n : ℝ)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun n : ℕ => (-2 : ℝ) * (1 / (n : ℝ))) (h := fun _ : ℕ => (0 : ℝ))
      ?_ ?_ ?_ ?_
    · have h : Tendsto (fun n : ℕ => (-2 : ℝ) * (1 / (n : ℝ))) atTop (nhds ((-2 : ℝ) * 0)) :=
        tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
      simpa using h
    · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hx0 : 0 ≤ Real.exp (S n) - 1 := exp_S_sub_one_nonneg n
      have hlt : Real.exp (S n) - 1 < (F n : ℝ) + 1 := by
        simpa [F] using (Nat.lt_floor_add_one (Real.exp (S n) - 1) : Real.exp (S n) - 1 < (⌊Real.exp (S n) - 1⌋₊ : ℝ) + 1)
      have hlow : -2 < (F n : ℝ) - Real.exp (S n) := by linarith
      calc
        (-2 : ℝ) * (1 / (n : ℝ)) = (-2 : ℝ) / (n : ℝ) := by ring
        _ ≤ ((F n : ℝ) - Real.exp (S n)) / (n : ℝ) := by
          exact div_le_div_of_nonneg_right (le_of_lt hlow) (le_of_lt hnpos)
    · filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hx0 : 0 ≤ Real.exp (S n) - 1 := exp_S_sub_one_nonneg n
      have hfloor : (F n : ℝ) ≤ Real.exp (S n) - 1 := by
        simpa [F] using (Nat.floor_le hx0 : (⌊Real.exp (S n) - 1⌋₊ : ℝ) ≤ Real.exp (S n) - 1)
      have hle : (F n : ℝ) - Real.exp (S n) ≤ 0 := by linarith
      exact div_nonpos_of_nonpos_of_nonneg hle (le_of_lt hnpos)
  have hmain := tendsto_exp_S_div.add herr
  have hcongr : (fun n : ℕ => Real.exp (S n) / (n : ℝ) + ((F n : ℝ) - Real.exp (S n)) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (F n : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hn]
    ring
  simpa using hmain.congr' hcongr

lemma tendsto_succ_ratio :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) := by
  have hcongr : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => 1 + 1 / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [Nat.cast_add_one]
    field_simp [hn]
  have hlim : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  simpa using hlim.congr' hcongr.symm

lemma tendsto_F_succ_div :
    Tendsto (fun n : ℕ => (F (n+1) : ℝ) / (n : ℝ)) atTop
      (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have h1 : Tendsto (fun n : ℕ => (F (n+1) : ℝ) / ((n+1 : ℕ) : ℝ)) atTop
      (nhds (Real.exp Real.eulerMascheroniConstant)) := by
    simpa [(Function.comp_def)] using (tendsto_F_div.comp (Filter.tendsto_add_atTop_nat 1))
  have hprod := h1.mul tendsto_succ_ratio
  have hcongr : (fun n : ℕ => (F (n+1) : ℝ) / ((n+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => (F (n+1) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hs : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hn, hs]
  simpa using hprod.congr' hcongr

lemma sum_A206911_diff (N : ℕ) :
    (∑ n ∈ range N, A206911_diff (n+1)) = (A206911 (N+1) : ℤ) - (A206911 1 : ℤ) := by
  simpa [A206911_diff, add_assoc] using
    (Finset.sum_range_sub (fun i : ℕ => (A206911 (i+1) : ℤ)) N)

lemma sum_A206911_diff_counts (N : ℕ) :
    (∑ n ∈ range N, A206911_diff (n+1)) = (2 : ℤ) * (N : ℤ) + (count_threes N : ℤ) := by
  calc
    (∑ n ∈ range N, A206911_diff (n+1))
        = ∑ n ∈ range N, ((2 : ℤ) + (if A206911_diff (n+1) = 3 then (1 : ℤ) else 0)) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases h3 : A206911_diff (n+1) = 3
          · simp [h3]
          · have h23 := A206911_diff_all (n+1) (Nat.succ_pos n)
            rcases h23 with h2 | h3'
            · simp [h2, h3]
            · contradiction
    _ = (2 : ℤ) * (N : ℤ) + (count_threes N : ℤ) := by
          simp [Finset.sum_add_distrib, count_threes, mul_comm]

lemma count_threes_int_formula (N : ℕ) :
    (count_threes N : ℤ) = (F (N+1) : ℤ) - (N : ℤ) - 1 := by
  have h1 := sum_A206911_diff N
  have h2 := sum_A206911_diff_counts N
  have h : (2 : ℤ) * (N : ℤ) + (count_threes N : ℤ) = (A206911 (N+1) : ℤ) - (A206911 1 : ℤ) := by
    rw [← h2]
    exact h1
  rw [A206911_int_eq_F, A206911_val_one] at h
  omega

lemma count_threes_le (N : ℕ) : count_threes N ≤ N := by
  rw [count_threes]
  have hle : (range N).sum (fun n => if A206911_diff (n+1) = 3 then (1 : ℕ) else 0) ≤ (range N).sum (fun _ => (1 : ℕ)) := by
    apply Finset.sum_le_sum
    intro n hn
    by_cases h : A206911_diff (n+1) = 3 <;> simp [h]
  simpa using hle

lemma count_twos_int_formula (N : ℕ) :
    (count_twos N : ℤ) = (2 : ℤ) * (N : ℤ) + 1 - (F (N+1) : ℤ) := by
  rw [count_twos]
  have hle := count_threes_le N
  have hct := count_threes_int_formula N
  have hsub : ((N - count_threes N : ℕ) : ℤ) = (N : ℤ) - (count_threes N : ℤ) := by
    exact_mod_cast (Nat.cast_sub hle : ((N - count_threes N : ℕ) : ℤ) = (N : ℤ) - (count_threes N : ℤ))
  rw [hsub, hct]
  ring

lemma tendsto_count_threes_div :
    Tendsto (fun N : ℕ => (count_threes N : ℝ) / (N : ℝ)) atTop
      (nhds (Real.exp Real.eulerMascheroniConstant - 1)) := by
  have hconst1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hlim := (tendsto_F_succ_div.sub hconst1).sub tendsto_one_div_atTop_nhds_zero_nat
  have hcongr : (fun N : ℕ => (F (N+1) : ℝ) / (N : ℝ) - 1 - 1 / (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => (count_threes N : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
    have hreal : (count_threes N : ℝ) = (F (N+1) : ℝ) - (N : ℝ) - 1 := by
      exact_mod_cast count_threes_int_formula N
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    rw [hreal]
    field_simp [hN']
  simpa [sub_eq_add_neg] using hlim.congr' hcongr

lemma tendsto_count_twos_div :
    Tendsto (fun N : ℕ => (count_twos N : ℝ) / (N : ℝ)) atTop
      (nhds (2 - Real.exp Real.eulerMascheroniConstant)) := by
  have hlim := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).add tendsto_one_div_atTop_nhds_zero_nat).sub tendsto_F_succ_div
  have hcongr : (fun N : ℕ => 2 + 1 / (N : ℝ) - (F (N+1) : ℝ) / (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => (count_twos N : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
    have hreal : (count_twos N : ℝ) = (2 : ℝ) * (N : ℝ) + 1 - (F (N+1) : ℝ) := by
      exact_mod_cast count_twos_int_formula N
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    rw [hreal]
    field_simp [hN']
  simpa [sub_eq_add_neg] using hlim.congr' hcongr

lemma tendsto_ratio_threes_to_twos :
    Tendsto ratio_threes_to_twos atTop
      (nhds ((Real.exp Real.eulerMascheroniConstant - 1) / (2 - Real.exp Real.eulerMascheroniConstant))) := by
  let c := Real.exp Real.eulerMascheroniConstant
  have hc_bounds := exp_gamma_bounds
  have hdenpos : 0 < 2 - c := by dsimp [c]; nlinarith [hc_bounds.2]
  have hden_ne : 2 - c ≠ 0 := ne_of_gt hdenpos
  have hq := tendsto_count_threes_div.div tendsto_count_twos_div hden_ne
  have hnonzero : ∀ᶠ N : ℕ in atTop, (count_twos N : ℝ) / (N : ℝ) ≠ 0 :=
    tendsto_count_twos_div.eventually_ne hden_ne
  have hcongr : (fun N : ℕ => (count_threes N : ℝ) / (N : ℝ) / ((count_twos N : ℝ) / (N : ℝ))) =ᶠ[atTop]
      ratio_threes_to_twos := by
    filter_upwards [hnonzero, eventually_ne_atTop (0 : ℕ)] with N htw hN
    have htw_nat : count_twos N ≠ 0 := by
      intro hz
      simp [hz] at htw
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    rw [ratio_threes_to_twos, if_neg htw_nat]
    field_simp [hN']
  simpa [c] using hq.congr' hcongr

lemma ratio_limit_bounds :
    3.5 < (Real.exp Real.eulerMascheroniConstant - 1) / (2 - Real.exp Real.eulerMascheroniConstant) ∧
    (Real.exp Real.eulerMascheroniConstant - 1) / (2 - Real.exp Real.eulerMascheroniConstant) < 3.6 := by
  let c := Real.exp Real.eulerMascheroniConstant
  have hc1 : (16/9 : ℝ) < c := by simpa [c] using exp_gamma_bounds.1
  have hc2 : c < (41/23 : ℝ) := by simpa [c] using exp_gamma_bounds.2
  have hden : 0 < 2 - c := by nlinarith
  constructor
  · rw [show (3.5 : ℝ) = 7/2 by norm_num]
    rw [lt_div_iff₀ hden]
    nlinarith
  · rw [show (3.6 : ℝ) = 18/5 by norm_num]
    rw [div_lt_iff₀ hden]
    nlinarith

end A206911_Work



/--
Conjecture: the difference sequence of A206911 consists of 2s and 3s,
and the ratio (number of 3s)/(number of 2s) tends to a number between 3.5 and 3.6.
-/
theorem oeis_a206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n ∈ ({2, 3} : Set ℤ)) ∧
  (∃ l : ℝ,
    3.5 < l ∧ l < 3.6 ∧
    Tendsto ratio_threes_to_twos atTop (nhds l)) := by
  constructor
  · intro n hn
    rcases A206911_Work.A206911_diff_all n hn with h | h
    · simp [h]
    · simp [h]
  · refine ⟨(Real.exp Real.eulerMascheroniConstant - 1) / (2 - Real.exp Real.eulerMascheroniConstant), ?_, ?_, ?_⟩
    · exact A206911_Work.ratio_limit_bounds.1
    · exact A206911_Work.ratio_limit_bounds.2
    · exact A206911_Work.tendsto_ratio_threes_to_twos
