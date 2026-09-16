import Mathlib
set_option linter.unusedVariables false
open Filter Asymptotics Topology Complex

noncomputable def A114362 (n : ℕ) : ℕ :=
  if h : n = 0 then
    2
  else
    let B_4n : ℚ := bernoulli (4 * n)
    let B_2n : ℚ := bernoulli (2 * n)
    let binom_qn : ℚ := ↑(Nat.choose (4 * n) (2 * n))
    let Q_n : ℚ := -2 * B_4n / (B_2n * B_2n * binom_qn)
    Q_n.num.natAbs

noncomputable def A114362_t (n : ℕ) : ℝ :=
  (riemannZeta (2 * (n : ℂ))).re / ((riemannZeta (n : ℂ)).re ^ 2)

lemma inv_sq_le (k : ℕ) (hk : 2 ≤ k) : (1 : ℝ) / (k : ℝ)^2 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkm1 : 0 < (k : ℝ) - 1 := by
    have : (1:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 1 < k)
    linarith
  have H : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) = 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
    rw [div_sub_div _ _ (ne_of_gt hkm1) (ne_of_gt hk0)]
    have h_eq : ((k : ℝ) - 1) * (k : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by ring
    rw [h_eq]
    congr 1
    ring
  rw [H]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

lemma sum_telescoping_K (K N : ℕ) (hK : 2 ≤ K) :
    ∑ k ∈ Finset.range N, (1 / ((k:ℝ) + (K:ℝ) - 1) - 1 / ((k:ℝ) + (K:ℝ))) = 1 / ((K - 1 : ℕ):ℝ) - 1 / ((N + K - 1:ℕ):ℝ) := by
  induction' N with m hm
  · have h1 : ((0 + K - 1 : ℕ) : ℝ) = ((K - 1 : ℕ) : ℝ) := by congr 1; omega
    rw [Finset.sum_range_zero, h1, sub_self]
  · rw [Finset.sum_range_succ, hm]
    have h2 : ((m + K - 1 : ℕ) : ℝ) = (m:ℝ) + (K:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    rw [h2]
    have h3 : ((m + 1 + K - 1 : ℕ) : ℝ) = (m:ℝ) + (K:ℝ) := by
      have : m + 1 + K - 1 = m + K := by omega
      rw [this, Nat.cast_add]
    rw [h3]
    ring

lemma tail_bound_K (n K : ℕ) (hn : 2 ≤ n) (hK : 2 ≤ K) :
    ∑' (k : ℕ), 1 / ((k:ℝ) + (K:ℝ))^n ≤ (1 / ((K - 1:ℕ):ℝ)) * (1 / (K:ℝ)^(n - 2)) := by
  have h_pos : ∀ m : ℕ, 0 ≤ 1 / ((m:ℝ) + (K:ℝ))^n := by intro m; positivity
  apply Real.tsum_le_of_sum_range_le h_pos
  intro N
  calc ∑ k ∈ Finset.range N, 1 / ((k:ℝ) + (K:ℝ))^n
    _ ≤ ∑ k ∈ Finset.range N, (1 / ((k:ℝ) + (K:ℝ))^2) * (1 / (K:ℝ)^(n-2)) := by
      apply Finset.sum_le_sum
      intro k _
      have h1 : ((k:ℝ) + (K:ℝ)) ^ n = ((k:ℝ) + (K:ℝ)) ^ 2 * ((k:ℝ) + (K:ℝ)) ^ (n - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h1, one_div, mul_inv, ← one_div, ← one_div]
      apply mul_le_mul_of_nonneg_left
      · apply one_div_le_one_div_of_le
        · positivity
        · have : (K:ℝ) ≤ ((k:ℝ) + (K:ℝ)) := by
            have h0 : (0:ℝ) ≤ (k:ℝ) := by positivity
            linarith
          have hpow : (K:ℝ)^(n-2) ≤ ((k:ℝ) + (K:ℝ))^(n-2) := by
            gcongr
          exact hpow
      · positivity
    _ = (∑ k ∈ Finset.range N, 1 / ((k:ℝ) + (K:ℝ))^2) * (1 / (K:ℝ)^(n-2)) := by
      rw [Finset.sum_mul]
    _ ≤ (∑ k ∈ Finset.range N, (1 / ((k:ℝ) + (K:ℝ) - 1) - 1 / ((k:ℝ) + (K:ℝ)))) * (1 / (K:ℝ)^(n-2)) := by
      apply mul_le_mul_of_nonneg_right
      · apply Finset.sum_le_sum
        intro k _
        have hk2 : 2 ≤ k + K := by omega
        have hk_cast : ((k + K:ℕ):ℝ) = (k:ℝ) + (K:ℝ) := by rw [Nat.cast_add]
        have := inv_sq_le (k + K) hk2
        rw [hk_cast] at this
        exact this
      · positivity
    _ = (1 / ((K - 1:ℕ):ℝ) - 1 / ((N + K - 1:ℕ):ℝ)) * (1 / (K:ℝ)^(n-2)) := by
      rw [sum_telescoping_K K N hK]
    _ ≤ (1 / ((K - 1:ℕ):ℝ)) * (1 / (K:ℝ)^(n-2)) := by
      apply mul_le_mul_of_nonneg_right
      · simp only [sub_le_self_iff]
        positivity
      · positivity

lemma O_tail (K : ℕ) (hK : 11 ≤ K) :
    (fun n : ℕ => (1 / ((K - 1:ℕ):ℝ)) * (1 / (K:ℝ)^(n - 2))) =O[atTop]
    (fun n : ℕ => 1 / (11:ℝ)^n) := by
  have H1 : (fun n : ℕ => (1 / (K:ℝ)^(n - 2))) =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
    apply Asymptotics.isBigO_of_le' _ (c := (11:ℝ)^2)
    intro n
    by_cases hn : 2 ≤ n
    · have hpow : (11:ℝ)^(n-2) ≤ (K:ℝ)^(n-2) := by
        gcongr
        exact_mod_cast hK
      have h1 : (11:ℝ)^n = (11:ℝ)^2 * (11:ℝ)^(n-2) := by
        rw [← pow_add]
        congr 1
        omega
      have hnon1 : 0 ≤ 1 / (K:ℝ)^(n-2) := by positivity
      have hnon2 : 0 ≤ 1 / (11:ℝ)^n := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnon1, Real.norm_eq_abs, abs_of_nonneg hnon2]
      rw [h1]
      have h_calc : (11:ℝ)^2 * (1 / ((11:ℝ)^2 * (11:ℝ)^(n-2))) = 1 / (11:ℝ)^(n-2) := by
        calc (11:ℝ)^2 * (1 / ((11:ℝ)^2 * (11:ℝ)^(n-2)))
          _ = ((11:ℝ)^2 * (1 / (11:ℝ)^2)) * (1 / (11:ℝ)^(n-2)) := by ring
          _ = 1 * (1 / (11:ℝ)^(n-2)) := by
            congr 1
            exact mul_one_div_cancel (by norm_num)
          _ = 1 / (11:ℝ)^(n-2) := by ring
      rw [h_calc]
      apply one_div_le_one_div_of_le
      · positivity
      · exact hpow
    · have : (1:ℝ) / (K:ℝ)^(n - 2) = 1 := by
        have : n - 2 = 0 := by omega
        rw [this]
        simp
      have hnon1 : 0 ≤ 1 / (K:ℝ)^(n-2) := by positivity
      rw [this, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
      have : 1 ≤ 121 * ‖1 / (11:ℝ) ^ n‖ := by
        have hnon2 : 0 ≤ 1 / (11:ℝ)^n := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hnon2]
        have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl
        · norm_num
        · norm_num
      have H11 : (11:ℝ)^2 = 121 := by norm_num
      rw [H11]
      exact this
  exact H1.const_mul_left _

lemma sum_add_tsum_nat_add_eq (f : ℕ → ℝ) (hf : Summable f) (K : ℕ) :
    ∑' (k : ℕ), f k = (∑ k ∈ Finset.range K, f k) + ∑' (k : ℕ), f (k + K) := by
  exact (hf.sum_add_tsum_nat_add K).symm

lemma O_of_le_11 {v : ℝ} (hv : 11 ≤ v) :
    (fun n : ℕ => 1 / v ^ n) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  refine Asymptotics.isBigO_of_le _ (fun n => ?_)
  have h1 : 0 ≤ 1 / v ^ n := by positivity
  have h2 : 0 ≤ 1 / (11:ℝ) ^ n := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h1, Real.norm_eq_abs, abs_of_nonneg h2]
  apply one_div_le_one_div_of_le
  · positivity
  · gcongr

lemma term_eq (n p q r s : ℕ) :
    ((1:ℝ) / 2 ^ n) ^ p * (1 / 3 ^ n) ^ q * (1 / 5 ^ n) ^ r * (1 / 7 ^ n) ^ s =
    1 / ((2^p * 3^q * 5^r * 7^s : ℕ) : ℝ) ^ n := by
  push_cast
  simp_rw [one_div_pow, one_div]
  rw [← mul_inv, ← mul_inv, ← mul_inv]
  congr 1
  simp_rw [← pow_mul, mul_comm n _]
  simp_rw [pow_mul]
  rw [← mul_pow, ← mul_pow, ← mul_pow]

lemma O_term (p q r s : ℕ) (h : 11 ≤ 2^p * 3^q * 5^r * 7^s) :
    (fun n : ℕ => ((1:ℝ) / 2 ^ n) ^ p * (1 / 3 ^ n) ^ q * (1 / 5 ^ n) ^ r * (1 / 7 ^ n) ^ s) =O[atTop]
    (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  simp_rw [term_eq]
  apply O_of_le_11
  exact_mod_cast h
lemma num_term_0 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^4) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^4) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 0 0 0
  norm_num

lemma num_term_1 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^5) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^5) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^5 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 5 0 0 0
  norm_num

lemma num_term_2 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^6) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^6) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^6 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 6 0 0 0
  norm_num

lemma num_term_3 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^7) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^7) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^7 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 7 0 0 0
  norm_num

lemma num_term_4 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -b^4) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -b^4) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^4 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 4 0 0
  norm_num

lemma num_term_5 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -b^5) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -b^5) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^5 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 5 0 0
  norm_num

lemma num_term_6 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -d^2) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 0 2 0
  norm_num

lemma num_term_7 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -d^3) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -d^3) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^3 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 0 3 0
  norm_num

lemma num_term_8 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -f_var^2) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 0 0 2
  norm_num

lemma num_term_9 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -f_var^3) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -f_var^3) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^3)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 0 0 3
  norm_num

lemma num_term_10 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * b^3) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * b^3) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^3 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 3 0 0
  norm_num

lemma num_term_11 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^6 * b) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^6 * b) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^6 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 6 1 0 0
  norm_num

lemma num_term_12 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^6 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^6 * d) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^6 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 6 0 1 0
  norm_num

lemma num_term_13 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -b^4 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -b^4 * d) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^4 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 4 1 0
  norm_num

lemma num_term_14 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^6 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^6 * f_var) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^6 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 6 0 0 1
  norm_num

lemma num_term_15 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -b^4 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -b^4 * f_var) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^4 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 4 0 1
  norm_num

lemma num_term_16 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^2 * d^3) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^2 * d^3) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^3 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 0 3 0
  norm_num

lemma num_term_17 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -5 * a^4 * b) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -5 * a^4 * b) =
    (fun n : ℕ => (-5:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 1 0 0
  norm_num

lemma num_term_18 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -5 * a^4 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -5 * a^4 * d) =
    (fun n : ℕ => (-5:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 0 1 0
  norm_num

lemma num_term_19 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -5 * a^4 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -5 * a^4 * f_var) =
    (fun n : ℕ => (-5:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 0 0 1
  norm_num

lemma num_term_20 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -5 * a^2 * b^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -5 * a^2 * b^2) =
    (fun n : ℕ => (-5:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 2 0 0
  norm_num

lemma num_term_21 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -5 * a^2 * b^3) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -5 * a^2 * b^3) =
    (fun n : ℕ => (-5:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^3 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 3 0 0
  norm_num

lemma num_term_22 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -5 * a^2 * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -5 * a^2 * d^2) =
    (fun n : ℕ => (-5:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 0 2 0
  norm_num

lemma num_term_23 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -5 * a^3 * b^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -5 * a^3 * b^2) =
    (fun n : ℕ => (-5:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 2 0 0
  norm_num

lemma num_term_24 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -5 * a^3 * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -5 * a^3 * d^2) =
    (fun n : ℕ => (-5:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 0 2 0
  norm_num

lemma num_term_25 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a * b^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a * b^2) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 2 0 0
  norm_num

lemma num_term_26 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a * b^3) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a * b^3) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^3 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 3 0 0
  norm_num

lemma num_term_27 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^2 * b) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^2 * b) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 1 0 0
  norm_num

lemma num_term_28 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^3 * b) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^3 * b) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 1 0 0
  norm_num

lemma num_term_29 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^5 * b) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^5 * b) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^5 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 5 1 0 0
  norm_num

lemma num_term_30 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^2 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^2 * d) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 0 1 0
  norm_num

lemma num_term_31 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^3 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^3 * d) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 0 1 0
  norm_num

lemma num_term_32 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^5 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^5 * d) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^5 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 5 0 1 0
  norm_num

lemma num_term_33 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * b^2 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * b^2 * d) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 2 1 0
  norm_num

lemma num_term_34 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * b^3 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * b^3 * d) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^3 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 3 1 0
  norm_num

lemma num_term_35 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^2 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^2 * f_var) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 0 0 1
  norm_num

lemma num_term_36 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^3 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^3 * f_var) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 0 0 1
  norm_num

lemma num_term_37 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * b^2 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * b^2 * f_var) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 2 0 1
  norm_num

lemma num_term_38 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * b^3 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * b^3 * f_var) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^3 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 3 0 1
  norm_num

lemma num_term_39 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^4 * b^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^4 * b^2) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 2 0 0
  norm_num

lemma num_term_40 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * a * b^4) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * a * b^4) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^4 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 4 0 0
  norm_num

lemma num_term_41 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * a * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * a * d^2) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 0 2 0
  norm_num

lemma num_term_42 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * a * f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * a * f_var^2) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 0 0 2
  norm_num

lemma num_term_43 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * b * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * b * d^2) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 1 2 0
  norm_num

lemma num_term_44 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * b * f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * b * f_var^2) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 1 0 2
  norm_num

lemma num_term_45 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * d * f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * d * f_var^2) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 0 1 2
  norm_num

lemma num_term_46 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * d^2 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * d^2 * f_var) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 0 2 1
  norm_num

lemma num_term_47 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 0 0 1
  norm_num

lemma num_term_48 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a * d^3) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a * d^3) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^3 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 0 3 0
  norm_num

lemma num_term_49 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * b * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * b * d) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 1 1 0
  norm_num

lemma num_term_50 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * b * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * b * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 1 0 1
  norm_num

lemma num_term_51 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * d * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 0 1 1
  norm_num

lemma num_term_52 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^5 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^5 * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^5 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 5 0 0 1
  norm_num

lemma num_term_53 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^2 * f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^2 * f_var^2) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 0 0 2
  norm_num

lemma num_term_54 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^3 * b^3) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^3 * b^3) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^3 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 3 0 0
  norm_num

lemma num_term_55 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^3 * f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^3 * f_var^2) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 0 0 2
  norm_num

lemma num_term_56 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^4 * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^4 * d^2) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 0 2 0
  norm_num

lemma num_term_57 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * b^2 * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * b^2 * d^2) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 2 2 0
  norm_num

lemma num_term_58 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * b^2 * f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * b^2 * f_var^2) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 2 0 2
  norm_num

lemma num_term_59 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -a^2 * d^2 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^2 * d^2 * f_var) =
    (fun n : ℕ => (-1:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 0 2 1
  norm_num

lemma num_term_60 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -10 * a^2 * b * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -10 * a^2 * b * d) =
    (fun n : ℕ => (-10:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 1 1 0
  norm_num

lemma num_term_61 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -10 * a^3 * b * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -10 * a^3 * b * d) =
    (fun n : ℕ => (-10:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 1 1 0
  norm_num

lemma num_term_62 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -8 * a * b^2 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -8 * a * b^2 * d) =
    (fun n : ℕ => (-8:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 2 1 0
  norm_num

lemma num_term_63 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -8 * a * b^2 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -8 * a * b^2 * f_var) =
    (fun n : ℕ => (-8:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 2 0 1
  norm_num

lemma num_term_64 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -8 * a^2 * b * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -8 * a^2 * b * f_var) =
    (fun n : ℕ => (-8:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 1 0 1
  norm_num

lemma num_term_65 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -8 * a^2 * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -8 * a^2 * d * f_var) =
    (fun n : ℕ => (-8:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 0 1 1
  norm_num

lemma num_term_66 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -7 * a^2 * b^2 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -7 * a^2 * b^2 * d) =
    (fun n : ℕ => (-7:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 2 1 0
  norm_num

lemma num_term_67 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -6 * a * b * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -6 * a * b * d) =
    (fun n : ℕ => (-6:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 1 1 0
  norm_num

lemma num_term_68 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -6 * a * b * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -6 * a * b * f_var) =
    (fun n : ℕ => (-6:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 1 0 1
  norm_num

lemma num_term_69 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -6 * a * b * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -6 * a * b * d^2) =
    (fun n : ℕ => (-6:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 1 2 0
  norm_num

lemma num_term_70 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -6 * a * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -6 * a * d * f_var) =
    (fun n : ℕ => (-6:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 0 1 1
  norm_num

lemma num_term_71 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -6 * b * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -6 * b * d * f_var) =
    (fun n : ℕ => (-6:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 1 1 1
  norm_num

lemma num_term_72 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -6 * a^3 * b * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -6 * a^3 * b * f_var) =
    (fun n : ℕ => (-6:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 1 0 1
  norm_num

lemma num_term_73 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -6 * a^3 * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -6 * a^3 * d * f_var) =
    (fun n : ℕ => (-6:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 0 1 1
  norm_num

lemma num_term_74 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a * b^3 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a * b^3 * d) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^3 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 3 1 0
  norm_num

lemma num_term_75 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a * d^2 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a * d^2 * f_var) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 0 2 1
  norm_num

lemma num_term_76 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * a^4 * b * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * a^4 * b * d) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 1 1 0
  norm_num

lemma num_term_77 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -4 * b^2 * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -4 * b^2 * d * f_var) =
    (fun n : ℕ => (-4:ℝ) * (((1:ℝ)/2^n)^0 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 0 2 1 1
  norm_num

lemma num_term_78 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * a^2 * b * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * a^2 * b * d^2) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 1 2 0
  norm_num

lemma num_term_79 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -3 * a^2 * b^2 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -3 * a^2 * b^2 * f_var) =
    (fun n : ℕ => (-3:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 2 0 1
  norm_num

lemma num_term_80 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a * b * f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a * b * f_var^2) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 1 0 2
  norm_num

lemma num_term_81 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a * d * f_var^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a * d * f_var^2) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^2)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 0 1 2
  norm_num

lemma num_term_82 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a * b^3 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a * b^3 * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^3 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 3 0 1
  norm_num

lemma num_term_83 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a * b^2 * d^2) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a * b^2 * d^2) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^2 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 2 2 0
  norm_num

lemma num_term_84 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^4 * b * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^4 * b * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 1 0 1
  norm_num

lemma num_term_85 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^4 * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^4 * d * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^4 * ((1:ℝ)/3^n)^0 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 4 0 1 1
  norm_num

lemma num_term_86 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^3 * b^2 * d) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^3 * b^2 * d) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^0)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 2 1 0
  norm_num

lemma num_term_87 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^3 * b^2 * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^3 * b^2 * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^3 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^0 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 3 2 0 1
  norm_num

lemma num_term_88 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -8 * a * b * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -8 * a * b * d * f_var) =
    (fun n : ℕ => (-8:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 1 1 1
  norm_num

lemma num_term_89 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a * b^2 * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a * b^2 * d * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^1 * ((1:ℝ)/3^n)^2 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 1 2 1 1
  norm_num

lemma num_term_90 : (fun n : ℕ => 
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    -2 * a^2 * b * d * f_var) =O[atTop] (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H : (fun n : ℕ => 
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -2 * a^2 * b * d * f_var) =
    (fun n : ℕ => (-2:ℝ) * (((1:ℝ)/2^n)^2 * ((1:ℝ)/3^n)^1 * ((1:ℝ)/5^n)^1 * ((1:ℝ)/7^n)^1)) := by
    ext n; dsimp only; ring
  rw [H]
  apply Asymptotics.IsBigO.const_mul_left
  apply O_term 2 1 1 1
  norm_num

lemma numerator_O :
    (fun n : ℕ =>
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let c := a^2; let d := (1:ℝ) / 5^n;
      let e := a*b; let f_var := (1:ℝ) / 7^n; let g := a^3; let h := b^2; let i := a*d;
      let P0 := a + b + c + d + e + f_var + g + h + i;
      let Q0 := c + h;
      let P := a + b + d + f_var;
      (1 + P0)^2 - (1 + Q0) - P * ((1 + P0)^2 + (1 + Q0))) =O[atTop]
    (fun n : ℕ => 1 / (11:ℝ) ^ n) := by
  have H_eq : (fun n : ℕ =>
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let c := a^2; let d := (1:ℝ) / 5^n;
      let e := a*b; let f_var := (1:ℝ) / 7^n; let g := a^3; let h := b^2; let i := a*d;
      let P0 := a + b + c + d + e + f_var + g + h + i;
      let Q0 := c + h;
      let P := a + b + d + f_var;
      (1 + P0)^2 - (1 + Q0) - P * ((1 + P0)^2 + (1 + Q0))) =
    (fun n : ℕ =>
      let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
      -a^4 + -a^5 + -a^6 + -a^7 + -b^4 + -b^5 + -d^2 + -d^3 + -f_var^2 + -f_var^3 + -2 * b^3 + -a^6 * b + -a^6 * d + -b^4 * d + -a^6 * f_var + -b^4 * f_var + -a^2 * d^3 + -5 * a^4 * b + -5 * a^4 * d + -5 * a^4 * f_var + -5 * a^2 * b^2 + -5 * a^2 * b^3 + -5 * a^2 * d^2 + -5 * a^3 * b^2 + -5 * a^3 * d^2 + -4 * a * b^2 + -4 * a * b^3 + -4 * a^2 * b + -4 * a^3 * b + -4 * a^5 * b + -4 * a^2 * d + -4 * a^3 * d + -4 * a^5 * d + -4 * b^2 * d + -4 * b^3 * d + -4 * a^2 * f_var + -4 * a^3 * f_var + -4 * b^2 * f_var + -4 * b^3 * f_var + -4 * a^4 * b^2 + -3 * a * b^4 + -3 * a * d^2 + -3 * a * f_var^2 + -3 * b * d^2 + -3 * b * f_var^2 + -3 * d * f_var^2 + -3 * d^2 * f_var + -2 * a * f_var + -2 * a * d^3 + -2 * b * d + -2 * b * f_var + -2 * d * f_var + -2 * a^5 * f_var + -2 * a^2 * f_var^2 + -2 * a^3 * b^3 + -2 * a^3 * f_var^2 + -2 * a^4 * d^2 + -2 * b^2 * d^2 + -2 * b^2 * f_var^2 + -a^2 * d^2 * f_var + -10 * a^2 * b * d + -10 * a^3 * b * d + -8 * a * b^2 * d + -8 * a * b^2 * f_var + -8 * a^2 * b * f_var + -8 * a^2 * d * f_var + -7 * a^2 * b^2 * d + -6 * a * b * d + -6 * a * b * f_var + -6 * a * b * d^2 + -6 * a * d * f_var + -6 * b * d * f_var + -6 * a^3 * b * f_var + -6 * a^3 * d * f_var + -4 * a * b^3 * d + -4 * a * d^2 * f_var + -4 * a^4 * b * d + -4 * b^2 * d * f_var + -3 * a^2 * b * d^2 + -3 * a^2 * b^2 * f_var + -2 * a * b * f_var^2 + -2 * a * d * f_var^2 + -2 * a * b^3 * f_var + -2 * a * b^2 * d^2 + -2 * a^4 * b * f_var + -2 * a^4 * d * f_var + -2 * a^3 * b^2 * d + -2 * a^3 * b^2 * f_var + -8 * a * b * d * f_var + -2 * a * b^2 * d * f_var + -2 * a^2 * b * d * f_var) := by
    ext n; dsimp only; ring
  rw [H_eq]
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  apply Asymptotics.IsBigO.add
  · exact num_term_0
  · exact num_term_1
  · exact num_term_2
  · exact num_term_3
  · exact num_term_4
  · exact num_term_5
  · exact num_term_6
  · exact num_term_7
  · exact num_term_8
  · exact num_term_9
  · exact num_term_10
  · exact num_term_11
  · exact num_term_12
  · exact num_term_13
  · exact num_term_14
  · exact num_term_15
  · exact num_term_16
  · exact num_term_17
  · exact num_term_18
  · exact num_term_19
  · exact num_term_20
  · exact num_term_21
  · exact num_term_22
  · exact num_term_23
  · exact num_term_24
  · exact num_term_25
  · exact num_term_26
  · exact num_term_27
  · exact num_term_28
  · exact num_term_29
  · exact num_term_30
  · exact num_term_31
  · exact num_term_32
  · exact num_term_33
  · exact num_term_34
  · exact num_term_35
  · exact num_term_36
  · exact num_term_37
  · exact num_term_38
  · exact num_term_39
  · exact num_term_40
  · exact num_term_41
  · exact num_term_42
  · exact num_term_43
  · exact num_term_44
  · exact num_term_45
  · exact num_term_46
  · exact num_term_47
  · exact num_term_48
  · exact num_term_49
  · exact num_term_50
  · exact num_term_51
  · exact num_term_52
  · exact num_term_53
  · exact num_term_54
  · exact num_term_55
  · exact num_term_56
  · exact num_term_57
  · exact num_term_58
  · exact num_term_59
  · exact num_term_60
  · exact num_term_61
  · exact num_term_62
  · exact num_term_63
  · exact num_term_64
  · exact num_term_65
  · exact num_term_66
  · exact num_term_67
  · exact num_term_68
  · exact num_term_69
  · exact num_term_70
  · exact num_term_71
  · exact num_term_72
  · exact num_term_73
  · exact num_term_74
  · exact num_term_75
  · exact num_term_76
  · exact num_term_77
  · exact num_term_78
  · exact num_term_79
  · exact num_term_80
  · exact num_term_81
  · exact num_term_82
  · exact num_term_83
  · exact num_term_84
  · exact num_term_85
  · exact num_term_86
  · exact num_term_87
  · exact num_term_88
  · exact num_term_89
  · exact num_term_90

lemma P0_eq (n : ℕ) :
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let c := a^2; let d := (1:ℝ) / 5^n;
    let e := a*b; let f_var := (1:ℝ) / 7^n; let g := a^3; let h := b^2; let i := a*d;
    a + b + c + d + e + f_var + g + h + i =
    1/(2:ℝ)^n + 1/(3:ℝ)^n + 1/(4:ℝ)^n + 1/(5:ℝ)^n + 1/(6:ℝ)^n + 1/(7:ℝ)^n + 1/(8:ℝ)^n + 1/(9:ℝ)^n + 1/(10:ℝ)^n := by
  dsimp only
  have hc : ((1:ℝ) / 2^n)^2 = 1 / (4:ℝ)^n := by
    calc ((1:ℝ) / 2^n)^2 = 1 / ((2:ℝ)^n)^2 := by rw [div_pow, one_pow]
      _ = 1 / ((2:ℝ)^2)^n := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 1 / (4:ℝ)^n := by norm_num
  have he : ((1:ℝ) / 2^n) * ((1:ℝ) / 3^n) = 1 / (6:ℝ)^n := by
    calc ((1:ℝ) / 2^n) * ((1:ℝ) / 3^n) = 1 / ((2:ℝ)^n * (3:ℝ)^n) := by rw [one_div_mul_one_div]
      _ = 1 / (2 * 3 : ℝ)^n := by rw [mul_pow]
      _ = 1 / (6:ℝ)^n := by norm_num
  have hg : ((1:ℝ) / 2^n)^3 = 1 / (8:ℝ)^n := by
    calc ((1:ℝ) / 2^n)^3 = 1 / ((2:ℝ)^n)^3 := by rw [div_pow, one_pow]
      _ = 1 / ((2:ℝ)^3)^n := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 1 / (8:ℝ)^n := by norm_num
  have hh : ((1:ℝ) / 3^n)^2 = 1 / (9:ℝ)^n := by
    calc ((1:ℝ) / 3^n)^2 = 1 / ((3:ℝ)^n)^2 := by rw [div_pow, one_pow]
      _ = 1 / ((3:ℝ)^2)^n := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 1 / (9:ℝ)^n := by norm_num
  have hi : ((1:ℝ) / 2^n) * ((1:ℝ) / 5^n) = 1 / (10:ℝ)^n := by
    calc ((1:ℝ) / 2^n) * ((1:ℝ) / 5^n) = 1 / ((2:ℝ)^n * (5:ℝ)^n) := by rw [one_div_mul_one_div]
      _ = 1 / (2 * 5 : ℝ)^n := by rw [mul_pow]
      _ = 1 / (10:ℝ)^n := by norm_num
  rw [hc, he, hg, hh, hi]

lemma Q0_eq (n : ℕ) :
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let c := a^2; let h := b^2;
    c + h = 1/(4:ℝ)^n + 1/(9:ℝ)^n := by
  dsimp only
  have hc : ((1:ℝ) / 2^n)^2 = 1 / (4:ℝ)^n := by
    calc ((1:ℝ) / 2^n)^2 = 1 / ((2:ℝ)^n)^2 := by rw [div_pow, one_pow]
      _ = 1 / ((2:ℝ)^2)^n := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 1 / (4:ℝ)^n := by norm_num
  have hh : ((1:ℝ) / 3^n)^2 = 1 / (9:ℝ)^n := by
    calc ((1:ℝ) / 3^n)^2 = 1 / ((3:ℝ)^n)^2 := by rw [div_pow, one_pow]
      _ = 1 / ((3:ℝ)^2)^n := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 1 / (9:ℝ)^n := by norm_num
  rw [hc, hh]

lemma P_eq (n : ℕ) :
    let a := (1:ℝ) / 2^n; let b := (1:ℝ) / 3^n; let d := (1:ℝ) / 5^n; let f_var := (1:ℝ) / 7^n;
    a + b + d + f_var = 1/(2:ℝ)^n + 1/(3:ℝ)^n + 1/(5:ℝ)^n + 1/(7:ℝ)^n := by
  dsimp only

lemma O_div_denom_eventually (N D : ℕ → ℝ) (hD : ∀ n ≥ 2, 1 ≤ D n) (hN : (fun n => N n) =O[atTop] (fun n => 1 / (11:ℝ)^n)) :
    (fun n => N n / D n) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
  have H_le : (fun n => N n / D n) =O[atTop] (fun n => N n) := by
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.eventually_atTop.mpr
    use 2
    intro n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    have hdpos : 0 < D n := by linarith [hD n hn]
    have h1 : |D n| = D n := abs_of_pos hdpos
    rw [h1]
    have h2 : 1 / D n ≤ 1 := by
      rw [div_le_iff₀ hdpos]
      linarith [hD n hn]
    calc |N n| / D n = |N n| * (1 / D n) := by ring
      _ ≤ |N n| * 1 := by
        apply mul_le_mul_of_nonneg_left h2
        exact abs_nonneg _
      _ = 1 * |N n| := by ring
  exact H_le.trans hN

lemma Z1_eq (n : ℕ) (hn : 2 ≤ n) :
    ∑' (k : ℕ), 1 / (k:ℝ)^n =
    (1 + 1/(2:ℝ)^n + 1/(3:ℝ)^n + 1/(4:ℝ)^n + 1/(5:ℝ)^n + 1/(6:ℝ)^n + 1/(7:ℝ)^n + 1/(8:ℝ)^n + 1/(9:ℝ)^n + 1/(10:ℝ)^n) +
    ∑' (k : ℕ), 1 / ((k + 11:ℕ):ℝ)^n := by
  have h_sum : Summable (fun (k:ℕ) => 1 / (k:ℝ)^n) := by
    apply Real.summable_one_div_nat_pow.mpr
    linarith
  have h_eq := (h_sum.sum_add_tsum_nat_add 11).symm
  have H0 : (0:ℝ)^n = 0 := by exact zero_pow (by omega)
  have H1 : (1:ℝ)^n = 1 := by exact one_pow n
  have H_sum_10 : ∑ k ∈ Finset.range 11, (1 / (k:ℝ)^n) = 1 + 1/(2:ℝ)^n + 1/(3:ℝ)^n + 1/(4:ℝ)^n + 1/(5:ℝ)^n + 1/(6:ℝ)^n + 1/(7:ℝ)^n + 1/(8:ℝ)^n + 1/(9:ℝ)^n + 1/(10:ℝ)^n := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    rw [H0, H1]
    norm_num
  rw [H_sum_10] at h_eq
  exact h_eq

lemma Z2_eq (n : ℕ) (hn : 2 ≤ n) :
    ∑' (k : ℕ), 1 / (k:ℝ)^(2*n) =
    (1 + 1/(4:ℝ)^n + 1/(9:ℝ)^n) +
    ∑' (k : ℕ), 1 / ((k + 4:ℕ):ℝ)^(2*n) := by
  have h_sum : Summable (fun (k:ℕ) => 1 / (k:ℝ)^(2*n)) := by
    apply Real.summable_one_div_nat_pow.mpr
    linarith
  have h_eq := (h_sum.sum_add_tsum_nat_add 4).symm
  have H0 : (0:ℝ)^(2*n) = 0 := by exact zero_pow (by omega)
  have H1 : (1:ℝ)^(2*n) = 1 := by exact one_pow (2*n)
  have H_sum_3 : ∑ k ∈ Finset.range 4, (1 / (k:ℝ)^(2*n)) = 1 + 1/(4:ℝ)^n + 1/(9:ℝ)^n := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    rw [H0, H1]
    have h2 : (2:ℝ)^(2*n) = (4:ℝ)^n := by
      calc (2:ℝ)^(2*n) = ((2:ℝ)^2)^n := by rw [pow_mul]
        _ = (4:ℝ)^n := by norm_num
    have h3 : (3:ℝ)^(2*n) = (9:ℝ)^n := by
      calc (3:ℝ)^(2*n) = ((3:ℝ)^2)^n := by rw [pow_mul]
        _ = (9:ℝ)^n := by norm_num
    rw [h2, h3]
    norm_num
  rw [H_sum_3] at h_eq
  exact h_eq

lemma eventuallyEq_Z_sub (Z1 Z2 P0 Q0 E1 E2 P : ℕ → ℝ)
    (hZ1 : ∀ n ≥ 2, Z1 n = 1 + P0 n + E1 n)
    (hZ2 : ∀ n ≥ 2, Z2 n = 1 + Q0 n + E2 n) :
    (fun n => Z1 n ^ 2 - Z2 n - P n * (Z1 n ^ 2 + Z2 n)) =ᶠ[Filter.atTop]
    (fun n => (1 + P0 n + E1 n) ^ 2 - (1 + Q0 n + E2 n) - P n * ((1 + P0 n + E1 n) ^ 2 + (1 + Q0 n + E2 n))) := by
  apply Filter.eventually_atTop.mpr
  use 2
  intro n hn
  dsimp only
  rw [hZ1 n hn, hZ2 n hn]

lemma eventuallyEq_frac_sub (Z1 Z2 P : ℕ → ℝ) (hZ : ∀ n ≥ 2, Z1 n ^ 2 + Z2 n ≠ 0) :
    (fun n => (Z1 n ^ 2 - Z2 n) / (Z1 n ^ 2 + Z2 n) - P n) =ᶠ[Filter.atTop]
    (fun n => (Z1 n ^ 2 - Z2 n - P n * (Z1 n ^ 2 + Z2 n)) / (Z1 n ^ 2 + Z2 n)) := by
  apply Filter.eventually_atTop.mpr
  use 2
  intro n hn
  dsimp only
  calc (Z1 n ^ 2 - Z2 n) / (Z1 n ^ 2 + Z2 n) - P n
    _ = (Z1 n ^ 2 - Z2 n) / (Z1 n ^ 2 + Z2 n) - P n * (Z1 n ^ 2 + Z2 n) / (Z1 n ^ 2 + Z2 n) := by
      congr 1
      exact (mul_div_cancel_right₀ _ (hZ n hn)).symm
    _ = (Z1 n ^ 2 - Z2 n - P n * (Z1 n ^ 2 + Z2 n)) / (Z1 n ^ 2 + Z2 n) := by rw [← sub_div]

lemma O_one_of_O_11 (E : ℕ → ℝ) (hE : E =O[atTop] (fun n => 1 / (11:ℝ)^n)) :
    E =O[atTop] (fun _ => (1:ℝ)) := by
  have H : (fun n : ℕ => 1 / (11:ℝ)^n) =O[atTop] (fun _ : ℕ => (1:ℝ)) := by
    apply Asymptotics.isBigO_of_le' _ (c := 1)
    intro n
    rw [Real.norm_eq_abs, norm_one]
    have : 0 ≤ 1 / (11:ℝ)^n := by positivity
    rw [abs_of_nonneg this]
    have h1 : (1:ℝ)^n = 1 := one_pow n
    have h2 : (1:ℝ)^n ≤ (11:ℝ)^n := by
      gcongr
      norm_num
    rw [h1] at h2
    have h3 : 1 / (11:ℝ)^n ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  exact hE.trans H

lemma O_one_of_pow (k : ℕ) : (fun n : ℕ => 1 / (k:ℝ)^n) =O[atTop] (fun _ => (1:ℝ)) := by
  apply Asymptotics.isBigO_of_le' _ (c := 1)
  intro n
  by_cases hk : k = 0
  · rw [hk]
    by_cases hn : n = 0
    · rw [hn]; norm_num
    · have h0 : (0:ℝ)^n = 0 := zero_pow (by omega)
      push_cast
      rw [h0]
      norm_num
  · rw [Real.norm_eq_abs, norm_one]
    have : 0 ≤ 1 / (k:ℝ)^n := by positivity
    rw [abs_of_nonneg this]
    have h1 : (1:ℝ)^n = 1 := one_pow n
    have h2 : (1:ℝ)^n ≤ (k:ℝ)^n := by
      gcongr
      exact_mod_cast (by omega : 1 ≤ k)
    rw [h1] at h2
    have h3 : 1 / (k:ℝ)^n ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

lemma tsum_ge_one (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ ∑' (k : ℕ), 1 / (k:ℝ)^n := by
  have H_sum : Summable (fun (k:ℕ) => 1 / (k:ℝ)^n) := by
    apply Real.summable_one_div_nat_pow.mpr
    linarith
  have h1 : (1:ℝ) = 1 / ((1:ℕ):ℝ)^n := by norm_num
  calc (1:ℝ) = 1 / ((1:ℕ):ℝ)^n := h1
    _ ≤ ∑' (k : ℕ), 1 / (k:ℝ)^n := by
      apply Summable.le_tsum H_sum 1
      intro j _
      positivity

lemma Z1_sq_add_Z2_ge_one (Z1 Z2 : ℝ) (hZ1 : 1 ≤ Z1) (hZ2 : 1 ≤ Z2) :
    1 ≤ Z1^2 + Z2 := by
  have : 1 ≤ Z1^2 := by
    calc (1:ℝ) = 1^2 := by norm_num
      _ ≤ Z1^2 := by
        gcongr
  linarith

lemma eventuallyEq_frac (Z1 Z2 P A : ℕ → ℝ) (hZ1 : ∀ n ≥ 2, Z1 n ≠ 0)
    (hA : ∀ n ≥ 2, A n = Z2 n / (Z1 n)^2) :
    (fun n => (1 - A n) / (1 + A n) - P n) =ᶠ[Filter.atTop]
    (fun n => ( (Z1 n)^2 - Z2 n) / ((Z1 n)^2 + Z2 n) - P n) := by
  apply Filter.eventually_atTop.mpr
  use 2
  intro n hn
  dsimp only
  rw [hA n hn]
  have H1 : (1 - Z2 n / (Z1 n)^2) / (1 + Z2 n / (Z1 n)^2) = ((Z1 n)^2 - Z2 n) / ((Z1 n)^2 + Z2 n) := by
    have h1 : 1 + Z2 n / (Z1 n)^2 = ((Z1 n)^2 + Z2 n) / (Z1 n)^2 := by
      calc 1 + Z2 n / (Z1 n)^2 = (Z1 n)^2 / (Z1 n)^2 + Z2 n / (Z1 n)^2 := by rw [div_self (pow_ne_zero 2 (hZ1 n hn))]
        _ = ((Z1 n)^2 + Z2 n) / (Z1 n)^2 := by rw [add_div]
    have h2 : 1 - Z2 n / (Z1 n)^2 = ((Z1 n)^2 - Z2 n) / (Z1 n)^2 := by
      calc 1 - Z2 n / (Z1 n)^2 = (Z1 n)^2 / (Z1 n)^2 - Z2 n / (Z1 n)^2 := by rw [div_self (pow_ne_zero 2 (hZ1 n hn))]
        _ = ((Z1 n)^2 - Z2 n) / (Z1 n)^2 := by rw [sub_div]
    rw [h1, h2]
    exact div_div_div_cancel_right₀ (pow_ne_zero 2 (hZ1 n hn)) ((Z1 n)^2 - Z2 n) ((Z1 n)^2 + Z2 n)
  rw [H1]

lemma isBigO_of_eventuallyEq (f1 f2 g : ℕ → ℝ)
    (h : f1 =ᶠ[atTop] f2)
    (hO : f2 =O[atTop] g) : f1 =O[atTop] g := by
  exact Filter.EventuallyEq.trans_isBigO h hO

lemma zeta_re (k : ℕ) (hk : 1 < k) : (riemannZeta (k:ℂ)).re = ∑' (n : ℕ), 1 / (n:ℝ)^k := by
  rw [zeta_nat_eq_tsum_of_gt_one hk]
  have h_sum : Summable (fun n : ℕ => 1 / (n:ℂ)^k) := by
    apply Summable.of_norm
    have H : Summable (fun n : ℕ => 1 / (n:ℝ)^k) := by
      apply Real.summable_one_div_nat_pow.mpr
      exact_mod_cast hk
    have h_eq : (fun (n : ℕ) => ‖1 / (n:ℂ)^k‖) = (fun n : ℕ => 1 / (n:ℝ)^k) := by
      ext n
      have h1 : ‖(1:ℂ)‖ = 1 := by norm_num
      rw [norm_div, h1, norm_pow, Complex.norm_natCast]
    rw [h_eq]
    exact H
  have H := Complex.re_tsum h_sum
  rw [H]
  congr 1
  ext n
  have h1 : (n:ℂ) = ((n:ℝ) : ℂ) := by push_cast; rfl
  rw [h1]
  have h2 : ((n:ℝ) : ℂ)^k = (((n:ℝ)^k : ℝ) : ℂ) := by push_cast; rfl
  rw [h2]
  have h3 : 1 / (((n:ℝ)^k : ℝ) : ℂ) = ((1 / (n:ℝ)^k : ℝ) : ℂ) := by push_cast; rfl
  rw [h3]
  exact Complex.ofReal_re _

lemma A114362_t_eq (n : ℕ) (hn : 2 ≤ n) :
    A114362_t n = (∑' (k : ℕ), 1 / (k:ℝ)^(2*n)) / (∑' (k : ℕ), 1 / (k:ℝ)^n)^2 := by
  dsimp [A114362_t]
  have h1 : 1 < n := by linarith
  have h2 : 1 < 2 * n := by linarith
  have H1 := zeta_re n h1
  have h_2n_c : 2 * (n:ℂ) = (2 * n : ℕ) := by push_cast; rfl
  rw [h_2n_c]
  have H2 := zeta_re (2 * n) h2
  rw [H1, H2]

theorem oeis_A114362_conjecture_1 :
  (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) - (1/2^n + 1/3^n + 1/5^n + 1/7^n)) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
  
  let a := fun n : ℕ => (1:ℝ) / 2^n
  let b := fun n : ℕ => (1:ℝ) / 3^n
  let c := fun n : ℕ => a n ^ 2
  let d := fun n : ℕ => (1:ℝ) / 5^n
  let e := fun n : ℕ => a n * b n
  let f_var := fun n : ℕ => (1:ℝ) / 7^n
  let g := fun n : ℕ => a n ^ 3
  let h := fun n : ℕ => b n ^ 2
  let i := fun n : ℕ => a n * d n
  
  let P0 := fun n : ℕ => a n + b n + c n + d n + e n + f_var n + g n + h n + i n
  let Q0 := fun n : ℕ => c n + h n
  let P := fun n : ℕ => a n + b n + d n + f_var n
  
  let Z1 := fun n : ℕ => ∑' (k : ℕ), 1 / (k:ℝ)^n
  let Z2 := fun n : ℕ => ∑' (k : ℕ), 1 / (k:ℝ)^(2*n)
  let E1 := fun n : ℕ => ∑' (k : ℕ), 1 / ((k + 11:ℕ):ℝ)^n
  let E2 := fun n : ℕ => ∑' (k : ℕ), 1 / ((k + 4:ℕ):ℝ)^(2*n)
  
  have H_eventually : (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) - P n) =ᶠ[atTop] (fun n => (Z1 n ^ 2 - Z2 n) / (Z1 n ^ 2 + Z2 n) - P n) := by
    apply eventuallyEq_frac Z1 Z2 P A114362_t
    · intro n hn
      have : 1 ≤ Z1 n := tsum_ge_one n hn
      linarith
    · exact A114362_t_eq

  have H_eventually2 : (fun n => (Z1 n ^ 2 - Z2 n) / (Z1 n ^ 2 + Z2 n) - P n) =ᶠ[atTop] (fun n => (Z1 n ^ 2 - Z2 n - P n * (Z1 n ^ 2 + Z2 n)) / (Z1 n ^ 2 + Z2 n)) := by
    apply eventuallyEq_frac_sub Z1 Z2 P
    intro n hn
    have h1 : 1 ≤ Z1 n := tsum_ge_one n hn
    have h2 : 1 ≤ Z2 n := tsum_ge_one (2*n) (by omega)
    have h3 : 1 ≤ Z1 n ^ 2 + Z2 n := Z1_sq_add_Z2_ge_one _ _ h1 h2
    linarith

  have H_eq : (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) - P n) =ᶠ[atTop] (fun n => (Z1 n ^ 2 - Z2 n - P n * (Z1 n ^ 2 + Z2 n)) / (Z1 n ^ 2 + Z2 n)) := H_eventually.trans H_eventually2

  have hP0 : P0 =O[atTop] (fun _ => (1:ℝ)) := by
    have H : P0 = fun n => 1/(2:ℝ)^n + 1/(3:ℝ)^n + 1/(4:ℝ)^n + 1/(5:ℝ)^n + 1/(6:ℝ)^n + 1/(7:ℝ)^n + 1/(8:ℝ)^n + 1/(9:ℝ)^n + 1/(10:ℝ)^n := by ext n; exact P0_eq n
    rw [H]
    repeat apply Asymptotics.IsBigO.add
    all_goals { apply O_one_of_pow }
  
  have hP : P =O[atTop] (fun _ => (1:ℝ)) := by
    have H : P = fun n => 1/(2:ℝ)^n + 1/(3:ℝ)^n + 1/(5:ℝ)^n + 1/(7:ℝ)^n := by ext n; exact P_eq n
    rw [H]
    repeat apply Asymptotics.IsBigO.add
    all_goals { apply O_one_of_pow }
  
  let N_poly := fun n : ℕ => (1 + P0 n)^2 - (1 + Q0 n) - P n * ((1 + P0 n)^2 + (1 + Q0 n))
  have hNO : N_poly =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
    have H : N_poly = (fun n : ℕ =>
      let a_loc := (1:ℝ) / 2^n; let b_loc := (1:ℝ) / 3^n; let c_loc := a_loc^2; let d_loc := (1:ℝ) / 5^n;
      let e_loc := a_loc*b_loc; let f_var_loc := (1:ℝ) / 7^n; let g_loc := a_loc^3; let h_loc := b_loc^2; let i_loc := a_loc*d_loc;
      let P0_loc := a_loc + b_loc + c_loc + d_loc + e_loc + f_var_loc + g_loc + h_loc + i_loc;
      let Q0_loc := c_loc + h_loc;
      let P_loc := a_loc + b_loc + d_loc + f_var_loc;
      (1 + P0_loc)^2 - (1 + Q0_loc) - P_loc * ((1 + P0_loc)^2 + (1 + Q0_loc))) := by ext n; rfl
    rw [H]
    exact numerator_O
  
  have hE1 : E1 =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
    have H : (fun n => ∑' (k : ℕ), 1 / ((k:ℝ) + (11:ℝ))^n) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
      have : (fun n => ∑' (k : ℕ), 1 / ((k:ℝ) + (11:ℝ))^n) =O[atTop] (fun n => (1 / ((11 - 1:ℕ):ℝ)) * (1 / (11:ℝ)^(n - 2))) := by
        rw [Asymptotics.isBigO_iff]
        use 1
        apply Filter.eventually_atTop.mpr
        use 2
        intro n hn
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        have h_pos : 0 ≤ ∑' (k : ℕ), 1 / ((k:ℝ) + (11:ℝ))^n := by positivity
        have h_pos2 : 0 ≤ (1 / ((11 - 1:ℕ):ℝ)) * (1 / (11:ℝ)^(n - 2)) := by positivity
        rw [abs_of_nonneg h_pos, abs_of_nonneg h_pos2]
        calc ∑' (k : ℕ), 1 / ((k:ℝ) + (11:ℝ))^n
          _ ≤ (1 / ((11 - 1:ℕ):ℝ)) * (1 / (11:ℝ)^(n - 2)) := tail_bound_K n 11 hn (by norm_num)
          _ = 1 * ((1 / ((11 - 1:ℕ):ℝ)) * (1 / (11:ℝ)^(n - 2))) := by ring
      exact this.trans (O_tail 11 (by norm_num))
    have h_eq : E1 = (fun n => ∑' (k : ℕ), 1 / ((k:ℝ) + (11:ℝ))^n) := by
      ext n; change ∑' (k:ℕ), 1 / (↑(k+11):ℝ)^n = ∑' (k:ℕ), 1 / (↑k+11:ℝ)^n; congr 1; funext k; push_cast; rfl
    rw [h_eq]
    exact H
    
  have hE2 : E2 =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
    have H : (fun n => ∑' (k : ℕ), 1 / ((k:ℝ) + (4:ℝ))^(2*n)) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
      have : (fun n => ∑' (k : ℕ), 1 / ((k:ℝ) + (4:ℝ))^(2*n)) =O[atTop] (fun n => (1 / ((4 - 1:ℕ):ℝ)) * (1 / (4:ℝ)^(2*n - 2))) := by
        rw [Asymptotics.isBigO_iff]
        use 1
        apply Filter.eventually_atTop.mpr
        use 2
        intro n hn
        have hn2 : 2 ≤ 2*n := by omega
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        have h_pos : 0 ≤ ∑' (k : ℕ), 1 / ((k:ℝ) + (4:ℝ))^(2*n) := by positivity
        have h_pos2 : 0 ≤ (1 / ((4 - 1:ℕ):ℝ)) * (1 / (4:ℝ)^(2*n - 2)) := by positivity
        rw [abs_of_nonneg h_pos, abs_of_nonneg h_pos2]
        calc ∑' (k : ℕ), 1 / ((k:ℝ) + (4:ℝ))^(2*n)
          _ ≤ (1 / ((4 - 1:ℕ):ℝ)) * (1 / (4:ℝ)^(2*n - 2)) := tail_bound_K (2*n) 4 hn2 (by norm_num)
          _ = 1 * ((1 / ((4 - 1:ℕ):ℝ)) * (1 / (4:ℝ)^(2*n - 2))) := by ring
      have H2 : (fun n => (1 / ((4 - 1:ℕ):ℝ)) * (1 / (4:ℝ)^(2*n - 2))) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
        apply Asymptotics.isBigO_of_le' _ (c := 16)
        intro n
        by_cases hn : 2 ≤ n
        · rw [Real.norm_eq_abs, Real.norm_eq_abs]
          have h_pos1 : 0 ≤ (1 / ((4 - 1:ℕ):ℝ)) * (1 / (4:ℝ)^(2*n - 2)) := by positivity
          have h_pos2 : 0 ≤ 1 / (11:ℝ)^n := by positivity
          rw [abs_of_nonneg h_pos1, abs_of_nonneg h_pos2]
          calc (1 / ((4 - 1:ℕ):ℝ)) * (1 / (4:ℝ)^(2*n - 2))
            _ = (1 / 3) * (1 / 16^(n - 1)) := by
              congr 1
              have h_eq : 2 * n - 2 = 2 * (n - 1) := by omega
              rw [h_eq, pow_mul]
              have h4 : (4:ℝ)^2 = 16 := by norm_num
              rw [h4]
            _ ≤ (1:ℝ) * (1 / 11^(n - 1)) := by
              have h1 : (1:ℝ) / 3 ≤ 1 := by norm_num
              have h2 : 1 / (16:ℝ)^(n - 1) ≤ 1 / (11:ℝ)^(n - 1) := by
                apply one_div_le_one_div_of_le (by positivity)
                have : (11:ℝ) ≤ 16 := by norm_num
                gcongr
              exact mul_le_mul h1 h2 (by positivity) (by norm_num)
            _ = 11 * (1 / 11^n) := by
              have h_eq_n : (11:ℝ)^n = 11 * 11^(n - 1) := by
                have : n = 1 + (n - 1) := by omega
                nth_rw 1 [this]
                rw [pow_add, pow_one]
              calc (1:ℝ) * (1 / 11^(n - 1)) = 11 * (1 / (11 * 11^(n-1))) := by ring
                _ = 11 * (1 / 11^n) := by rw [← h_eq_n]
            _ ≤ 16 * (1 / 11^n) := by
              apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        · have h_lt : n = 0 ∨ n = 1 := by omega
          rcases h_lt with rfl | rfl
          · norm_num
          · norm_num
      exact this.trans H2
    have h_eq : E2 = (fun n => ∑' (k : ℕ), 1 / ((k:ℝ) + (4:ℝ))^(2*n)) := by
      ext n; change ∑' (k:ℕ), 1 / (↑(k+4):ℝ)^(2*n) = ∑' (k:ℕ), 1 / (↑k+4:ℝ)^(2*n); congr 1; funext k; push_cast; rfl
    rw [h_eq]
    exact H
  
  have H_eventually3 : (fun n => Z1 n ^ 2 - Z2 n - P n * (Z1 n ^ 2 + Z2 n)) =ᶠ[atTop]
    (fun n => (1 + P0 n + E1 n) ^ 2 - (1 + Q0 n + E2 n) - P n * ((1 + P0 n + E1 n) ^ 2 + (1 + Q0 n + E2 n))) := by
    apply eventuallyEq_Z_sub Z1 Z2 P0 Q0 E1 E2 P
    · intro n hn
      have H := Z1_eq n hn
      have h_alg : 1 + 1 / 2 ^ n + 1 / 3 ^ n + 1 / 4 ^ n + 1 / 5 ^ n + 1 / 6 ^ n + 1 / 7 ^ n + 1 / 8 ^ n + 1 / 9 ^ n + 1 / 10 ^ n = 1 + P0 n := by
        have H2 := P0_eq n
        -- H2 is `P0 n = 1/2^n + ... + 1/10^n`
        -- wait, H2 is `a + ... = 1/2^n + ...`
        -- LHS of H2 is definitionally `P0 n`.
        change P0 n = 1 / 2 ^ n + 1 / 3 ^ n + 1 / 4 ^ n + 1 / 5 ^ n + 1 / 6 ^ n + 1 / 7 ^ n + 1 / 8 ^ n + 1 / 9 ^ n + 1 / 10 ^ n at H2
        rw [H2]
        ring
      linarith
    · intro n hn
      have H := Z2_eq n hn
      have h_alg : 1 + 1 / 4 ^ n + 1 / 9 ^ n = 1 + Q0 n := by
        have H2 := Q0_eq n
        change Q0 n = 1 / 4 ^ n + 1 / 9 ^ n at H2
        rw [H2]
        ring
      linarith

  have H_O_sum : (fun n => (1 + P0 n + E1 n) ^ 2 - (1 + Q0 n + E2 n) - P n * ((1 + P0 n + E1 n) ^ 2 + (1 + Q0 n + E2 n))) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
    have H_eq_N : (fun n => (1 + P0 n + E1 n) ^ 2 - (1 + Q0 n + E2 n) - P n * ((1 + P0 n + E1 n) ^ 2 + (1 + Q0 n + E2 n))) = 
      (fun n => N_poly n + E1 n * (2 + 2 * P0 n - 2 * P n - 2 * P n * P0 n) + E1 n ^ 2 * (1 - P n) + E2 n * (-1 - P n)) := by
      ext n; dsimp only; ring
    rw [H_eq_N]
    apply Asymptotics.IsBigO.add
    apply Asymptotics.IsBigO.add
    apply Asymptotics.IsBigO.add
    · exact hNO
    · have H_mul : (fun n => 2 + 2 * P0 n - 2 * P n - 2 * P n * P0 n) =O[atTop] (fun _ => (1:ℝ)) := by
        apply Asymptotics.IsBigO.sub
        apply Asymptotics.IsBigO.sub
        apply Asymptotics.IsBigO.add
        · exact isBigO_const_const (2:ℝ) (by norm_num) Filter.atTop
        · apply Asymptotics.IsBigO.const_mul_left hP0
        · apply Asymptotics.IsBigO.const_mul_left hP
        · have h_2PP0 : (fun n => 2 * P n * P0 n) = (fun n => 2 * (P n * P0 n)) := by ext n; ring
          rw [h_2PP0]
          apply Asymptotics.IsBigO.const_mul_left
          have h_mul2 := Asymptotics.IsBigO.mul hP hP0
          have h_eq : (fun (n : ℕ) => (1:ℝ) * 1) = fun n => (1:ℝ) := by ext n; ring
          rw [h_eq] at h_mul2
          exact h_mul2
      have H_prod := Asymptotics.IsBigO.mul hE1 H_mul
      have h_eq : (fun (n : ℕ) => 1 / (11:ℝ) ^ n * 1) = fun n => 1 / (11:ℝ) ^ n := by ext n; ring
      rw [h_eq] at H_prod
      exact H_prod
    · have H_E1_O1 : E1 =O[atTop] (fun _ => (1:ℝ)) := O_one_of_O_11 E1 hE1
      have H_E1_sq := Asymptotics.IsBigO.mul hE1 H_E1_O1
      have h_eq : (fun (n : ℕ) => 1 / (11:ℝ) ^ n * 1) = fun n => 1 / (11:ℝ) ^ n := by ext n; ring
      rw [h_eq] at H_E1_sq
      have H_mul : (fun n => 1 - P n) =O[atTop] (fun _ => (1:ℝ)) := by
        apply Asymptotics.IsBigO.sub
        · exact isBigO_const_const (1:ℝ) (by norm_num) Filter.atTop
        · exact hP
      have H_prod := Asymptotics.IsBigO.mul H_E1_sq H_mul
      rw [h_eq] at H_prod
      have H_sq : (fun n => E1 n ^ 2 * (1 - P n)) = fun n => E1 n * E1 n * (1 - P n) := by ext n; ring
      rw [H_sq]
      exact H_prod
    · have H_mul : (fun n => -1 - P n) =O[atTop] (fun _ => (1:ℝ)) := by
        apply Asymptotics.IsBigO.sub
        · exact isBigO_const_const (-1:ℝ) (by norm_num) Filter.atTop
        · exact hP
      have H_prod := Asymptotics.IsBigO.mul hE2 H_mul
      have h_eq : (fun (n : ℕ) => 1 / (11:ℝ) ^ n * 1) = fun n => 1 / (11:ℝ) ^ n := by ext n; ring
      rw [h_eq] at H_prod
      exact H_prod

  have H_num : (fun n => Z1 n ^ 2 - Z2 n - P n * (Z1 n ^ 2 + Z2 n)) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
    exact isBigO_of_eventuallyEq _ _ _ H_eventually3 H_O_sum

  have H_div : (fun n => (Z1 n ^ 2 - Z2 n - P n * (Z1 n ^ 2 + Z2 n)) / (Z1 n ^ 2 + Z2 n)) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
    apply O_div_denom_eventually _ _ _ H_num
    intro n hn
    have h1 : 1 ≤ Z1 n := tsum_ge_one n hn
    have h2 : 1 ≤ Z2 n := tsum_ge_one (2*n) (by omega)
    exact Z1_sq_add_Z2_ge_one _ _ h1 h2

  have heqP : (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) - (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n)) = (fun n => (1 - A114362_t n) / (1 + A114362_t n) - P n) := by
    ext n
    have hP : (1:ℝ) / 2 ^ n + 1 / 3 ^ n + 1 / 5 ^ n + 1 / 7 ^ n = P n := (P_eq n).symm
    rw [hP]
  rw [heqP]
  exact isBigO_of_eventuallyEq _ _ _ H_eq H_div


theorem oeis_A114362_conjecture_1.disproof :
  ¬ (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) - (1/2^n + 1/3^n + 1/5^n + 1/7^n)) =O[atTop] (fun n => 1 / (11:ℝ)^n) := by
  sorry
