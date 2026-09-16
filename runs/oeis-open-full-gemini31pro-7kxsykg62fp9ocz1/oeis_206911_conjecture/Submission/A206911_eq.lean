import Submission.Spec
import Submission.TestLimit

open Real Nat Finset Filter Topology

lemma harm_nonneg (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  induction' n with n ih
  · simp
  · rw [harmonic_succ]
    push_cast
    positivity

lemma a206911_S_n_eq_harmonic (n : ℕ) : (range n).sum (fun k => 1 / ((k : ℝ) + 1)) = harmonic n := by
  induction' n with n ih
  · simp
  · rw [sum_range_succ, ih, harmonic_succ]
    push_cast
    rw [one_div]

lemma A206911_eq (n : ℕ) : A206911 n = n + ⌊exp (harmonic n) - 1⌋₊ := by
  change n + ⌊rexp _ - 1⌋₊ = _
  rw [a206911_S_n_eq_harmonic]

lemma sum_diff_eq (N : ℕ) (h_mono : Monotone A206911) : (range N).sum (fun n => A206911_diff (n + 1)) = A206911 (N + 1) - A206911 1 := by
  induction' N with N ih
  · simp
  · rw [sum_range_succ, ih]
    have h1 : A206911 1 ≤ A206911 (N + 1) := h_mono (Nat.le_add_left 1 N)
    have h2 : A206911 (N + 1) ≤ A206911 (N + 1 + 1) := h_mono (Nat.le_succ _)
    change A206911 (N + 1) - A206911 1 + (A206911 (N + 1 + 1) - A206911 (N + 1)) = A206911 (N + 1 + 1) - A206911 1
    omega

lemma count_2s_add_count_3s_eq_N (N : ℕ) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    A206911_count_2s N + A206911_count_3s N = N := by
  dsimp [A206911_count_2s, A206911_count_3s]
  rw [← sum_add_distrib]
  have : ∀ n ∈ range N, (if A206911_diff (n + 1) = 2 then 1 else 0) + (if A206911_diff (n + 1) = 3 then 1 else 0) = 1 := by
    intro n _
    rcases h23 (n + 1) (Nat.le_add_left 1 n) with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [sum_congr rfl this, sum_const, card_range, smul_eq_mul, mul_one]

lemma sum_diff_eq_counts (N : ℕ) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    (range N).sum (fun n => A206911_diff (n + 1)) = 2 * A206911_count_2s N + 3 * A206911_count_3s N := by
  dsimp [A206911_count_2s, A206911_count_3s]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  have : ∀ n ∈ range N, A206911_diff (n + 1) = 2 * (if A206911_diff (n + 1) = 2 then 1 else 0) + 3 * (if A206911_diff (n + 1) = 3 then 1 else 0) := by
    intro n _
    rcases h23 (n + 1) (Nat.le_add_left 1 n) with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [sum_congr rfl this]

lemma count_3s_eq (N : ℕ) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    A206911_count_3s N = (range N).sum (fun n => A206911_diff (n + 1)) - 2 * N := by
  have h2 := sum_diff_eq_counts N h23
  have h3 := count_2s_add_count_3s_eq_N N h23
  omega

lemma count_2s_eq (N : ℕ) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    A206911_count_2s N = 3 * N - (range N).sum (fun n => A206911_diff (n + 1)) := by
  have h2 := sum_diff_eq_counts N h23
  have h3 := count_2s_add_count_3s_eq_N N h23
  omega

lemma tendsto_A206911_div_n : Tendsto (fun n : ℕ => (A206911 n : ℝ) / n) atTop (nhds (1 + exp eulerMascheroniConstant)) := by
  have H := tendsto_floor_exp_harmonic_div_n.const_add 1
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [A206911_eq]
  push_cast
  rw [add_div, div_self (Nat.cast_ne_zero.mpr hn)]
  congr 2
  have h_nonneg : 0 ≤ exp (harmonic n) - 1 := by
    have h_harm_nonneg : (0 : ℝ) ≤ harmonic n := harm_nonneg n
    have : 1 ≤ exp (harmonic n) := by
      have h_exp := Real.exp_monotone h_harm_nonneg
      rwa [Real.exp_zero] at h_exp
    linarith
  have h_fl : (⌊exp (harmonic n) - 1⌋₊ : ℤ) = ⌊exp (harmonic n) - 1⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.mpr h_nonneg)
  rw [← Int.cast_natCast ⌊exp (harmonic n) - 1⌋₊, h_fl]

lemma tendsto_A206911_succ_div_N : Tendsto (fun N : ℕ => (A206911 (N + 1) : ℝ) / N) atTop (nhds (1 + exp eulerMascheroniConstant)) := by
  have H := tendsto_A206911_div_n
  have H1 := H.comp (tendsto_add_atTop_nat 1)
  have H2 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (nhds 1) := by
    have H2a : Tendsto (fun N : ℕ => 1 + (N : ℝ)⁻¹) atTop (nhds 1) := by
      have hz : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have ha := hz.const_add 1
      rwa [add_zero] at ha
    apply Tendsto.congr' _ H2a
    filter_upwards [eventually_ne_atTop 0] with N hN
    push_cast
    rw [add_div, div_self (Nat.cast_ne_zero.mpr hN), one_div]
  have H3 := H1.mul H2
  rw [mul_one] at H3
  apply Tendsto.congr' _ H3
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hn_ne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp
  have : ((A206911 (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ)) * (((N + 1 : ℕ) : ℝ) / (N : ℝ)) = (A206911 (N + 1) : ℝ) / (N : ℝ) := by
    calc
      _ = (A206911 (N + 1) : ℝ) * ((N + 1 : ℕ) : ℝ)⁻¹ * (((N + 1 : ℕ) : ℝ) * (N : ℝ)⁻¹) := by rw [div_eq_mul_inv, div_eq_mul_inv]
      _ = (A206911 (N + 1) : ℝ) * (((N + 1 : ℕ) : ℝ)⁻¹ * ((N + 1 : ℕ) : ℝ)) * (N : ℝ)⁻¹ := by ring
      _ = (A206911 (N + 1) : ℝ) * 1 * (N : ℝ)⁻¹ := by rw [inv_mul_cancel₀ hn_ne]
      _ = (A206911 (N + 1) : ℝ) / (N : ℝ) := by rw [mul_one, ← div_eq_mul_inv]
  exact this

lemma tendsto_A206911_1_div_N : Tendsto (fun N : ℕ => (A206911 1 : ℝ) / N) atTop (nhds 0) := by
  have : (fun N : ℕ => (A206911 1 : ℝ) / N) = fun N : ℕ => (A206911 1 : ℝ) * (N : ℝ)⁻¹ := by
    ext N
    rw [div_eq_mul_inv]
  rw [this]
  have hz : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := hz.const_mul (A206911 1 : ℝ)
  rwa [mul_zero] at h

lemma tendsto_sum_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) / N) atTop (nhds (1 + exp eulerMascheroniConstant)) := by
  have H := tendsto_A206911_succ_div_N.sub tendsto_A206911_1_div_N
  rw [sub_zero] at H
  apply Tendsto.congr' _ H
  filter_upwards [] with N
  have h_sum := sum_diff_eq N h_mono
  have h_sum_real : ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) = (A206911 (N + 1) : ℝ) - (A206911 1 : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sub (h_mono (Nat.le_add_left 1 N)), ← h_sum]
  rw [h_sum_real]
  push_cast
  rw [sub_div]

lemma tendsto_c3_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / N) atTop (nhds (exp eulerMascheroniConstant - 1)) := by
  have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have H := (tendsto_sum_div_N h_mono h23).sub hc2
  have eq : 1 + exp eulerMascheroniConstant - 2 = exp eulerMascheroniConstant - 1 := by ring
  rw [eq] at H
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with N hn
  have h_c3 := count_3s_eq N h23
  have h2 : 2 * N ≤ (range N).sum (fun n => A206911_diff (n + 1)) := by
    have h2' : (range N).sum (fun _ => 2) ≤ (range N).sum (fun n => A206911_diff (n + 1)) := by
      apply sum_le_sum
      intro i _
      rcases h23 (i + 1) (Nat.le_add_left 1 i) with h | h
      · rw [h]
      · rw [h]; omega
    simp at h2'
    rw [mul_comm] at h2'
    exact h2'
  have h_cast : (A206911_count_3s N : ℝ) = ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) - 2 * N := by
    rw [h_c3, Nat.cast_sub h2, ← Nat.cast_sum]; push_cast; rfl
  rw [h_cast, sub_div]
  congr 1
  rw [mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]

lemma tendsto_c2_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => (A206911_count_2s N : ℝ) / N) atTop (nhds (2 - exp eulerMascheroniConstant)) := by
  have hc3 : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) := tendsto_const_nhds
  have H := hc3.sub (tendsto_sum_div_N h_mono h23)
  have eq : 3 - (1 + exp eulerMascheroniConstant) = 2 - exp eulerMascheroniConstant := by ring
  rw [eq] at H
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with N hn
  have h_c2 := count_2s_eq N h23
  have h3 : (range N).sum (fun n => A206911_diff (n + 1)) ≤ 3 * N := by
    have h3' : (range N).sum (fun n => A206911_diff (n + 1)) ≤ (range N).sum (fun _ => 3) := by
      apply sum_le_sum
      intro i _
      rcases h23 (i + 1) (Nat.le_add_left 1 i) with h | h
      · rw [h]; omega
      · rw [h]
    simp at h3'
    rw [mul_comm] at h3'
    exact h3'
  have h_cast : (A206911_count_2s N : ℝ) = 3 * N - ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) := by
    rw [h_c2, Nat.cast_sub h3, ← Nat.cast_sum]; push_cast; rfl
  rw [h_cast, sub_div]
  congr 1
  rw [mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]

lemma tendsto_ratio (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) (h_not_two : exp eulerMascheroniConstant ≠ 2) :
    Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds ((exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant))) := by
  have H := (tendsto_c3_div_N h_mono h23).div (tendsto_c2_div_N h_mono h23) (by exact sub_ne_zero.mpr h_not_two.symm)
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with N hn
  dsimp
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) (A206911_count_3s N : ℝ) (A206911_count_2s N : ℝ)

