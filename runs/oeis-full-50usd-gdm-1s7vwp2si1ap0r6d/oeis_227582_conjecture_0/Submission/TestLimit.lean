import FormalConjectures.Util.ProblemImports

open Filter Topology

lemma decreasing_limit_zero_pos (y : ℕ → ℝ) (h_dec : ∀ n, y (n + 1) < y n) (h_lim : Tendsto y atTop (nhds 0)) (n : ℕ) : y n > 0 := by
  by_cases h_ge : y (n + 1) ≥ 0
  · have : y n > y (n + 1) := h_dec n
    linarith
  · push_neg at h_ge -- now h_ge : y (n + 1) < 0
    have h_eps : (0 : ℝ) < - y (n + 1) := by linarith
    have h_lim' := h_lim
    rw [tendsto_atTop_nhds] at h_lim'
    rcases h_lim' (- y (n + 1)) h_eps with ⟨N, h_N⟩
    have h_mono : ∀ m, y (n + 1 + m) < y (n + 1) := by
      intro m
      induction m with
      | zero => exact h_dec (n + 1)
      | succ m ih =>
        have h_step := h_dec (n + 1 + m + 1)
        have h_eq : n + 1 + (m + 1) = n + 1 + m + 1 := by ring
        rw [h_eq]
        exact lt_trans h_step ih
    let m := N
    have h_ge_N : n + 1 + m ≥ N := by omega
    have h_bnd := h_N (n + 1 + m) h_ge_N
    have h_lt_y := h_mono m
    rw [Real.dist_0_eq_abs] at h_bnd
    have h_ym_neg : y (n + 1 + m) < 0 := by linarith
    have h_abs : |y (n + 1 + m)| = - y (n + 1 + m) := abs_of_neg h_ym_neg
    rw [h_abs] at h_bnd
    linarith

lemma increasing_limit_zero_neg (y : ℕ → ℝ) (h_inc : ∀ n, y n < y (n + 1)) (h_lim : Tendsto y atTop (nhds 0)) (n : ℕ) : y n < 0 := by
  have h_dec : ∀ n, - y (n + 1) < - y n := by
    intro k
    have := h_inc k
    linarith
  have h_lim_neg : Tendsto (fun k ↦ - y k) atTop (nhds 0) := by
    have h_id : (fun k ↦ - y k) = (fun x ↦ -x) ∘ y := rfl
    rw [h_id]
    have h_neg : Tendsto (fun x : ℝ ↦ -x) (nhds 0) (nhds 0) := by
      have : (fun x : ℝ ↦ -x) = fun x ↦ - (1:ℝ) * x := by ext; ring
      rw [this]
      -- wait, multiplication by a constant is continuous
      exact Tendsto.neg_const rfl
    exact Tendsto.neg h_lim
  have h_pos := decreasing_limit_zero_pos (fun k ↦ - y k) h_dec h_lim_neg n
  dsimp at h_pos
  linarith

lemma tendsto_index_atTop : Tendsto (fun n : ℕ ↦ n * n + n - 1) atTop atTop := by
  apply tendsto_atTop_mono (fun n ↦ (n : ℝ)) -- wait, we need it as ℕ → ℕ first
  · intro n
    show n ≤ n * n + n - 1
    rcases n with _ | n
    · simp
    · omega
  · exact tendsto_id

lemma tendsto_harmonic_sub_log_comp :
    Tendsto (fun n : ℕ ↦ (harmonic (n * n + n - 1) : ℝ) - log (n * n + n - 1)) atTop (nhds eulerMascheroniConstant) := by
  have h_comp := tendsto_harmonic_sub_log.comp tendsto_index_atTop
  exact h_comp

lemma tendsto_log_term : Tendsto (fun n : ℕ ↦ log (1 + 1 / (n * n + n - 1 : ℝ))) atTop (nhds 0) := by
  have h_index : Tendsto (fun n : ℕ ↦ (n * n + n - 1 : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n : ℕ ↦ (n : ℝ))
    · intro n
      rcases n with _ | n
      · simp
      · push_cast; linarith
    · exact tendsto_natCast_atTop_atTop
  have h_div : Tendsto (fun n : ℕ ↦ 1 / (n * n + n - 1 : ℝ)) atTop (nhds 0) := by
    have h_inv : (fun n : ℕ ↦ 1 / (n * n + n - 1 : ℝ)) = (fun x ↦ x⁻¹) ∘ (fun n : ℕ ↦ (n * n + n - 1 : ℝ)) := by
      ext n; simp [one_div]
    rw [h_inv]
    exact tendsto_inv_atTop_zero.comp h_index
  have h_add : Tendsto (fun n : ℕ ↦ 1 + 1 / (n * n + n - 1 : ℝ)) atTop (nhds 1) := by
    have h_one := tendsto_const_nhds (x := (1:ℝ))
    have h_sum := Tendsto.add h_one h_div
    rw [add_zero] at h_sum
    exact h_sum
  have h_log : ContinuousAt log 1 := continuousAt_log (by norm_num)
  have h_comp := h_log.tendsto.comp h_add
  rw [Real.log_one] at h_comp
  exact h_comp

def D_seq (n : ℕ) : ℝ :=
  2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ) - eulerMascheroniConstant

lemma h_LB (n : ℕ) (hn : 1 ≤ n) : 2 * log n - log (n * n + n - 1 : ℝ) < D_seq n := by
  unfold D_seq
  have h_gamma := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h_seq' : eulerMascheroniSeq' n = (harmonic n : ℝ) - log n := by
    unfold eulerMascheroniSeq'
    have : n ≠ 0 := by omega
    simp [this]
  rw [h_seq'] at h_gamma
  have h_sum_diff := harmonic_diff_eq_sum n (n * n + n - 1 - n)
  have h_sub_eq : n + (n * n + n - 1 - n) = n * n + n - 1 := by omega
  rw [h_sub_eq] at h_sum_diff
  have h_range_eq : (n * n + n - 1 - n) = (n * n - 1) := by omega
  rw [h_range_eq] at h_sum_diff
  have h_lt := sum_inv_lt_log_sub n (by omega) (n * n - 2)
  have h_range_eq2 : (n * n - 2 + 1) = (n * n - 1) := by omega
  rw [h_range_eq2] at h_lt
  rw [← h_sum_diff] at h_lt
  have h_lt_cast : (n + (n * n - 2) + 1 : ℝ) = (n * n + n - 1 : ℝ) := by
    push_cast; ring
  rw [h_lt_cast] at h_lt
  linarith

lemma h_UB (n : ℕ) (hn : 1 ≤ n) : D_seq n < 2 * log (n + 1) - log (n * n + n : ℝ) := by
  unfold D_seq
  have h_gamma := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  unfold eulerMascheroniSeq at h_gamma
  have h_sum_diff := harmonic_diff_eq_sum n (n * n + n - 1 - n)
  have h_sub_eq : n + (n * n + n - 1 - n) = n * n + n - 1 := by omega
  rw [h_sub_eq] at h_sum_diff
  have h_range_eq : (n * n + n - 1 - n) = (n * n - 1) := by omega
  rw [h_range_eq] at h_sum_diff
  have h_gt := sum_inv_gt_log_sub n (n * n - 2)
  have h_range_eq2 : (n * n - 2 + 1) = (n * n - 1) := by omega
  rw [h_range_eq2] at h_gt
  rw [← h_sum_diff] at h_gt
  have h_gt_cast : (n + (n * n - 2) + 2 : ℝ) = (n * n + n : ℝ) := by
    push_cast; ring
  rw [h_gt_cast] at h_gt
  linarith
lemma tendsto_LB_limit : Tendsto (fun n : ℕ ↦ 2 * log n - log (n * n + n - 1 : ℝ)) atTop (nhds 0) := by
  have h_eq : (fun n : ℕ ↦ 2 * log n - log (n * n + n - 1 : ℝ)) =
              (fun n : ℕ ↦ - log ( (n * n + n - 1 : ℝ) / ((n : ℝ) * (n : ℝ)) )) := by
    ext n
    rcases n with _ | n
    · simp
    · have hn : (n + 1 : ℝ) > 0 := by positivity
      have hnn : (n + 1 : ℝ) * (n + 1 : ℝ) > 0 := by positivity
      have h_idx : (n + 1 : ℝ) * (n + 1 : ℝ) + (n + 1 : ℝ) - 1 > 0 := by positivity
      have h_div : log (((n + 1 : ℝ) * (n + 1 : ℝ) + (n + 1 : ℝ) - 1) / ((n + 1 : ℝ) * (n + 1 : ℝ))) =
                   log ((n + 1 : ℝ) * (n + 1 : ℝ) + (n + 1 : ℝ) - 1) - log ((n + 1 : ℝ) * (n + 1 : ℝ)) := by
        exact log_div (by linarith) (by linarith)
      have h_mul : log ((n + 1 : ℝ) * (n + 1 : ℝ)) = 2 * log (n + 1) := by
        rw [log_mul (by linarith) (by linarith)]
        ring
      rw [h_div, h_mul]
      ring
  rw [h_eq]
  have h_div_eq : (fun n : ℕ ↦ ((n * n + n - 1 : ℝ) / ((n : ℝ) * (n : ℝ)))) =
                  (fun n : ℕ ↦ 1 + 1 / (n : ℝ) - 1 / ((n : ℝ) * (n : ℝ))) := by
    ext n
    rcases n with _ | n
    · simp
    · have hn : (n + 1 : ℝ) > 0 := by positivity
      have h_ne : (n + 1 : ℝ) * (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp; ring
  have h_lim : Tendsto (fun n : ℕ ↦ ( (n * n + n - 1 : ℝ) / ((n : ℝ) * (n : ℝ)) )) atTop (nhds 1) := by
    rw [h_div_eq]
    have h1 := tendsto_const_nhds (x := (1:ℝ))
    have h2 : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
    have h3 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) * (n : ℝ))) atTop (nhds 0) := by
      have h_inv : (fun n : ℕ ↦ 1 / ((n : ℝ) * (n : ℝ))) = (fun x ↦ x⁻¹) ∘ (fun n : ℕ ↦ (n : ℝ) * (n : ℝ)) := by
        ext n; simp [one_div]
      rw [h_inv]
      have h_index : Tendsto (fun n : ℕ ↦ (n : ℝ) * (n : ℝ)) atTop atTop := by
        exact tendsto_atTop_mono (fun n : ℕ ↦ (n : ℝ)) (by intro n; nlinarith) tendsto_natCast_atTop_atTop
      exact tendsto_inv_atTop_zero.comp h_index
    have h_sum := Tendsto.add h1 h2
    have h_sub := Tendsto.sub h_sum h3
    simp at h_sub
    exact h_sub
  have h_log : ContinuousAt log 1 := continuousAt_log (by norm_num)
  have h_comp := h_log.tendsto.comp h_lim
  rw [Real.log_one] at h_comp
  exact h_comp.neg

lemma tendsto_UB_limit : Tendsto (fun n : ℕ ↦ 2 * log (n + 1) - log (n * n + n : ℝ)) atTop (nhds 0) := by
  have h_eq : (fun n : ℕ ↦ 2 * log (n + 1) - log (n * n + n : ℝ)) =
              (fun n : ℕ ↦ - log (1 + 1 / (n + 1 : ℝ))) := by
    ext n
    rcases n with _ | n
    · simp
    · have hn : (n + 1 : ℝ) > 0 := by positivity
      have h_log_n_n_n : log ((n + 1 : ℝ) * (n + 1 : ℝ) + (n + 1 : ℝ)) = log (n + 1 : ℝ) + log (n + 2 : ℝ) := by
        have h_factor : (n + 1 : ℝ) * (n + 1 : ℝ) + (n + 1 : ℝ) = (n + 1 : ℝ) * (n + 2 : ℝ) := by ring
        rw [h_factor]
        exact log_mul (by positivity) (by positivity)
      have h_one_add : 1 + 1 / (n + 1 : ℝ) = (n + 2 : ℝ) / (n + 1 : ℝ) := by
        have : (n + 1 : ℝ) ≠ 0 := by positivity
        field_simp; ring
      have h_log_one_add : log (1 + 1 / (n + 1 : ℝ)) = log (n + 2 : ℝ) - log (n + 1 : ℝ) := by
        rw [h_one_add]
        exact log_div (by positivity) (by positivity)
      rw [h_log_n_n_n, h_log_one_add]
      ring
  rw [h_eq]
  have h_add : Tendsto (fun n : ℕ ↦ 1 + 1 / (n + 1 : ℝ)) atTop (nhds 1) := by
    have h1 := tendsto_const_nhds (x := (1:ℝ))
    have h2 : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
      have h_inv : (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) = (fun x ↦ x⁻¹) ∘ (fun n : ℕ ↦ (n + 1 : ℝ)) := by
        ext n; simp [one_div]
      rw [h_inv]
      have h_index : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
        exact tendsto_atTop_mono (fun n : ℕ ↦ (n : ℝ)) (by intro n; linarith) tendsto_natCast_atTop_atTop
      exact tendsto_inv_atTop_zero.comp h_index
    have h_sum := Tendsto.add h1 h2
    rw [add_zero] at h_sum
    exact h_sum
  have h_log : ContinuousAt log 1 := continuousAt_log (by norm_num)
  have h_comp := h_log.tendsto.comp h_add
  rw [Real.log_one] at h_comp
  exact h_comp.neg

lemma tendsto_D_atTop : Tendsto D_seq atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_LB_limit tendsto_UB_limit
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact le_of_lt (h_LB n hn)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact le_of_lt (h_UB n hn)

def L_seq (n : ℕ) : ℝ := 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ))

lemma L_diff_eq (n : ℕ) (hn : 2 ≤ n) : L_seq n - L_seq (n + 1) =
    5 / (3 * (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold L_seq
  have : (n : ℝ) > 0 := by positivity
  field_simp; ring

lemma refined_bound_gt_L_diff (n : ℕ) (hn : 2 ≤ n) :
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1) >
    L_seq n - L_seq (n + 1) := by
  rw [L_diff_eq n hn]
  have : (n : ℝ) ≥ 2 := by qify; exact hn
  have h_num_pos : 66*(n:ℝ)^4 + 264*(n:ℝ)^3 + 433*(n:ℝ)^2 + 338*(n:ℝ) + 99 > 0 := by positivity
  have h_den_pos : 3 * (18 * (n : ℝ)^9 + 162 * (n : ℝ)^8 + 645 * (n : ℝ)^7 + 1491 * (n : ℝ)^6 + 2210 * (n : ℝ)^5 + 2188 * (n : ℝ)^4 + 1453 * (n : ℝ)^3 + 623 * (n : ℝ)^2 + 154 * (n : ℝ) + 16) > 0 := by positivity
  have h_eq : ((4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
              (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1)) -
              5 / (3 * (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
              (66*(n:ℝ)^4 + 264*(n:ℝ)^3 + 433*(n:ℝ)^2 + 338*(n:ℝ) + 99) /
              (3 * (18 * (n : ℝ)^9 + 162 * (n : ℝ)^8 + 645 * (n : ℝ)^7 + 1491 * (n : ℝ)^6 + 2210 * (n : ℝ)^5 + 2188 * (n : ℝ)^4 + 1453 * (n : ℝ)^3 + 623 * (n : ℝ)^2 + 154 * (n : ℝ) + 16)) := by
    field_simp; ring
  rw [← sub_pos, h_eq]
  exact div_pos h_num_pos h_den_pos



def pairing_sum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2

lemma pairing_sum_eq (n : ℕ) : pairing_sum n = ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) / 3 := by
  induction n with
  | zero =>
    unfold pairing_sum
    simp
    ring
  | succ n ih =>
    unfold pairing_sum at ih ⊢
    rw [Finset.sum_range_succ']
    push_cast
    have h_shift : (fun i : ℕ ↦ (2 * ((n : ℝ) + 1) + 1 - 2 * ((i : ℝ) + 1))^2) =
                   (fun i : ℕ ↦ (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2) := by
      ext i
      ring
    rw [h_shift]
    rw [ih]
    ring



def T_LB5 (n : ℕ) : ℝ :=
  (5 * (n : ℝ)^2 + 10 * (n : ℝ) + 9) / (3 * ((n : ℝ) + 1)^5) +
  1 / (((n : ℝ) + 1)^6) +
  ((n : ℝ) * (2 * (n : ℝ) + 1) * (3 * (n : ℝ)^2 + 3 * (n : ℝ) - 1)) / (15 * ((n : ℝ) + 1)^9) +
  1 / (((n : ℝ) + 1)^7)

def U_seq (n : ℕ) : ℝ := 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)

def S_6 (n : ℝ) : ℝ :=
  (n + 1)^6 + n * (n + 1) * (2 * n + 1) * (3 * n^4 + 6 * n^3 - 3 * n + 1) / 21

def T_UB (n : ℕ) : ℝ :=
  (5 * (n : ℝ)^2 + 10 * (n : ℝ) + 9) / (3 * ((n : ℝ) + 1)^5) +
  1 / (((n : ℝ) + 1)^6) +
  ((n : ℝ) * (2 * (n : ℝ) + 1) * (3 * (n : ℝ)^2 + 3 * (n : ℝ) - 1)) / (15 * ((n : ℝ) + 1)^9) +
  1 / (((n : ℝ) + 1)^7) +
  S_6 (n : ℝ) / (((n : ℝ) + 1)^12 * ((n : ℝ)^2 + (n : ℝ)))

lemma T_UB_lt_U_diff (n : ℕ) (hn : 2 ≤ n) : T_UB n < U_seq n - U_seq (n + 1) := by
  unfold T_UB U_seq S_6
  have : (n : ℝ) ≥ 2 := by qify; exact hn
  have h_num : 1848*(n:ℝ)^12 + 20328*(n:ℝ)^11 + 102821*(n:ℝ)^10 + 314469*(n:ℝ)^9 + 648766*(n:ℝ)^8 +
               954670*(n:ℝ)^7 + 1029971*(n:ℝ)^6 + 823041*(n:ℝ)^5 + 487676*(n:ℝ)^4 + 212717*(n:ℝ)^3 +
               65848*(n:ℝ)^2 + 12865*(n:ℝ) + 1155 > 0 := by positivity
  have h_den : 105 * (n : ℝ) * (36 * (n : ℝ)^16 + 576 * (n : ℝ)^15 + 4272 * (n : ℝ)^14 + 19488 * (n : ℝ)^13 +
               61153 * (n : ℝ)^12 + 139788 * (n : ℝ)^11 + 240306 * (n : ℝ)^10 + 315964 * (n : ℝ)^9 +
               319671 * (n : ℝ)^8 + 247896 * (n : ℝ)^7 + 145068 * (n : ℝ)^6 + 61944 * (n : ℝ)^5 +
               17967 * (n : ℝ)^4 + 2908 * (n : ℝ)^3 + 18 * (n : ℝ)^2 - 84 * (n : ℝ) - 11) > 0 := by
    have : (n:ℝ) ≥ 2 := by linarith
    have : 18 * (n : ℝ)^2 - 84 * (n : ℝ) - 11 = 18 * (n : ℝ) * ((n : ℝ) - 2) - 48 * (n : ℝ) - 11 := by ring
    nlinarith
  have h_eq : (U_seq n - U_seq (n + 1)) - T_UB n =
              (1848*(n:ℝ)^12 + 20328*(n:ℝ)^11 + 102821*(n:ℝ)^10 + 314469*(n:ℝ)^9 + 648766*(n:ℝ)^8 +
               954670*(n:ℝ)^7 + 1029971*(n:ℝ)^6 + 823041*(n:ℝ)^5 + 487676*(n:ℝ)^4 + 212717*(n:ℝ)^3 +
               65848*(n:ℝ)^2 + 12865*(n:ℝ) + 1155) /
              (105 * (n : ℝ) * (36 * (n : ℝ)^16 + 576 * (n : ℝ)^15 + 4272 * (n : ℝ)^14 + 19488 * (n : ℝ)^13 +
               61153 * (n : ℝ)^12 + 139788 * (n : ℝ)^11 + 240306 * (n : ℝ)^10 + 315964 * (n : ℝ)^9 +
               319671 * (n : ℝ)^8 + 247896 * (n : ℝ)^7 + 145068 * (n : ℝ)^6 + 61944 * (n : ℝ)^5 +
               17967 * (n : ℝ)^4 + 2908 * (n : ℝ)^3 + 18 * (n : ℝ)^2 - 84 * (n : ℝ) - 11)) := by
    unfold U_seq S_6 T_UB
    field_simp; ring
  rw [← sub_pos, h_eq]
  exact div_pos h_num h_den


lemma T_LB5_gt_L_diff (n : ℕ) (hn : 2 ≤ n) : T_LB5 n > L_seq n - L_seq (n + 1) := by
  rw [L_diff_eq n hn]
  unfold T_LB5
  have : (n : ℝ) ≥ 2 := by qify; exact hn
  have h_pos : (n : ℝ) > 0 := by linarith
  have h_pos1 : (n : ℝ) + 1 > 0 := by linarith
  have h_pos2 : (n : ℝ) + 2 > 0 := by linarith
  have h_num : (n:ℝ)^6 + 6*(n:ℝ)^5 + 14*(n:ℝ)^4 + 16*(n:ℝ)^3 - 17*(n:ℝ)^2 - 50*(n:ℝ) - 25 =
               ((n:ℝ) - 2) * ((n:ℝ)^5 + 8*(n:ℝ)^4 + 30*(n:ℝ)^3 + 76*(n:ℝ)^2 + 135*(n:ℝ) + 220) + 415 := by ring
  have h_num_pos : (n:ℝ)^6 + 6*(n:ℝ)^5 + 14*(n:ℝ)^4 + 16*(n:ℝ)^3 - 17*(n:ℝ)^2 - 50*(n:ℝ) - 25 > 0 := by
    rw [h_num]
    have : (n : ℝ) - 2 ≥ 0 := by linarith
    have : (n:ℝ)^5 + 8*(n:ℝ)^4 + 30*(n:ℝ)^3 + 76*(n:ℝ)^2 + 135*(n:ℝ) + 220 > 0 := by positivity
    nlinarith
  -- now field_simp can clear denominators
  -- wait, let's use field_simp to convert the inequality to a numerator inequality
  -- to avoid field_simp making a giant mess, let's do it carefully
  have h_eq : T_LB5 n - (L_seq n - L_seq (n + 1)) =
              ((n:ℝ)^6 + 6*(n:ℝ)^5 + 14*(n:ℝ)^4 + 16*(n:ℝ)^3 - 17*(n:ℝ)^2 - 50*(n:ℝ) - 25) /
              (15 * (n : ℝ) * ((n : ℝ) + 1)^9 * ((n : ℝ) + 2)) := by
    unfold T_LB5
    rw [L_diff_eq n hn]
    -- verify with field_simp and ring
    field_simp; ring
  rw [← sub_pos, h_eq]
  have h_den_pos : 15 * (n : ℝ) * ((n : ℝ) + 1)^9 * ((n : ℝ) + 2) > 0 := by positivity
  exact div_pos h_num_pos h_den_pos

lemma sum_pairing (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) =
    ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) := by
  have h_split : ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) =
                 ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 2 * n + 1), (1 / (k : ℝ)) +
                 ∑ k ∈ Finset.Ico (n^2 + 2 * n + 1) (n^2 + 3 * n + 2), (1 / (k : ℝ)) := by
    rw [Finset.sum_Ico_consecutive]
    · omega
    · omega
  rw [h_split]
  have h1 : ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 2 * n + 1), (1 / (k : ℝ)) =
            ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ))) := by
    have h_ico : n^2 + 2 * n + 1 = (n^2 + n) + (n + 1) := by omega
    rw [h_ico]
    have h_range := Finset.sum_Ico_eq_sum_range (fun k : ℕ ↦ 1 / (k : ℝ)) (n^2 + n) (n + 1)
    rw [h_range]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    congr 2
    ring
  have h2 : ∑ k ∈ Finset.Ico (n^2 + 2 * n + 1) (n^2 + 3 * n + 2), (1 / (k : ℝ)) =
            ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) := by
    have h_ico : n^2 + 3 * n + 2 = (n^2 + 2 * n + 1) + (n + 1) := by omega
    rw [h_ico]
    have h_range := Finset.sum_Ico_eq_sum_range (fun k : ℕ ↦ 1 / (k : ℝ)) (n^2 + 2 * n + 1) (n + 1)
    rw [h_range]
    have h_congr : ∑ i ∈ Finset.range (n + 1), (1 / (((n^2 + 2 * n + 1) + i : ℕ) : ℝ)) =
                    ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + 2 * (n : ℝ) + 1 + (i : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      congr 2
      ring
    rw [h_congr]
    have h_reflect := Finset.sum_range_reflect (fun i : ℕ ↦ 1 / ((n : ℝ)^2 + 2 * (n : ℝ) + 1 + (i : ℝ))) (n + 1)
    rw [← h_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    have h_sub : n + 1 - 1 - i = n - i := by omega
    rw [h_sub]
    congr 2
    have : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := by
      have : i ≤ n := by omega
      exact Nat.cast_sub this
    rw [this]
    ring
  rw [h1, h2, ← Finset.sum_add_distrib]

lemma summand_le (n i : ℕ) (hi : i < n + 1) :
    1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) ≥
    4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
  have h_XY : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) ≤ ((n : ℝ) + 1)^4 := by
    have h_eq : ((n : ℝ) + 1)^4 - ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) =
                ((n : ℝ) + 1)^2 - 1/4 + ((i : ℝ) - (n : ℝ) - 1/2)^2 := by ring
    rw [← sub_nonneg]
    rw [h_eq]
    have h_sq : ((i : ℝ) - (n : ℝ) - 1/2)^2 ≥ 0 := by positivity
    have : (n : ℝ) ≥ 1 := by qify; omega
    nlinarith

  have h_posX : (n : ℝ)^2 + (n : ℝ) + (i : ℝ) > 0 := by positivity
  have h_posY : (n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ) > 0 := by
    have : (i : ℝ) ≤ (n : ℝ) := by qify; omega
    have : (n : ℝ) ≥ 1 := by qify; omega
    nlinarith
  have h_posSum : 2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1 > 0 := by positivity
  have h_posDen : ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) > 0 := by positivity
  have h_eq2 : 1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) -
              (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) =
              ((2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ) + 1)^4 - ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)))) /
              (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) := by
    field_simp; ring
  rw [ge_iff_le, ← sub_nonneg, h_eq2]
  have h_num_nonneg : (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ) + 1)^4 - ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) ≥ 0 := by
    have h1 : (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 ≥ 0 := by positivity
    have h2 : ((n : ℝ) + 1)^4 - ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) ≥ 0 := by linarith
    exact mul_nonneg h1 h2
  have h_den_pos : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) > 0 := by
    positivity
  exact div_nonneg h_num_nonneg (le_of_lt h_den_pos)
lemma summand_ge (n i : ℕ) (hi : i < n + 1) :
    1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) ≤
    4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
  have h_XY_ge : ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) ≤ ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) := by
    have h_eq : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) =
                (i : ℝ) * (2 * (n : ℝ) + 1 - (i : ℝ)) := by ring
    rw [← sub_nonneg]
    rw [h_eq]
    have : (i : ℝ) ≥ 0 := by positivity
    have : (i : ℝ) ≤ (n : ℝ) := by qify; omega
    have : (n : ℝ) ≥ 1 := by qify; omega
    nlinarith

  have h_posX : (n : ℝ)^2 + (n : ℝ) + (i : ℝ) > 0 := by positivity
  have h_posY : (n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ) > 0 := by
    have : (i : ℝ) ≤ (n : ℝ) := by qify; omega
    have : (n : ℝ) ≥ 1 := by qify; omega
    nlinarith
  have h_posSum : 2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1 > 0 := by positivity
  have h_posDen : ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) > 0 := by positivity
  have h_eq2 : 1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) -
              (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) =
              -(((2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1))) /
              (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)))) := by
    field_simp; ring
  rw [← sub_nonpos, h_eq2]
  have h_num_nonneg : (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1)) ≥ 0 := by
    have h1 : (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 ≥ 0 := by positivity
    have h2 : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) ≥ 0 := by linarith
    exact mul_nonneg h1 h2
  have h_den_pos : ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) > 0 := by
    positivity
  have h_div_nonneg : ((2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 * (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) - ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1))) /
                     (((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ)) * (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) ≥ 0 := by
    exact div_nonneg h_num_nonneg (le_of_lt h_den_pos)
  linarith


lemma pairing_sum_bound (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) ≥
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
  rw [← sum_pairing n]
  have h_le : ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) ≥
              ∑ i ∈ Finset.range (n + 1), (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    exact summand_le n i hi_lt
  have h_sum_eq : ∑ i ∈ Finset.range (n + 1), (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) =
                  (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
                  pairing_sum n / (((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_const]
      have : ((Finset.range (n + 1)).card : ℝ) = (n : ℝ) + 1 := by simp
      rw [this]
      ring
    · rw [← Finset.sum_div]
      congr 1
  rw [h_sum_eq]
  rw [pairing_sum_eq n]
  rfl
lemma refined_bound_gt_L_diff (n : ℕ) (hn : 2 ≤ n) :
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1) >
    L_seq n - L_seq (n + 1) := by
  rw [L_diff_eq n hn]
  have : (n : ℝ) ≥ 2 := by qify; exact hn
  have h_num_pos : 66*(n:ℝ)^4 + 264*(n:ℝ)^3 + 433*(n:ℝ)^2 + 338*(n:ℝ) + 99 > 0 := by positivity
  have h_den_pos : 3 * (18 * (n : ℝ)^9 + 162 * (n : ℝ)^8 + 645 * (n : ℝ)^7 + 1491 * (n : ℝ)^6 + 2210 * (n : ℝ)^5 + 2188 * (n : ℝ)^4 + 1453 * (n : ℝ)^3 + 623 * (n : ℝ)^2 + 154 * (n : ℝ) + 16) > 0 := by positivity
  have h_eq : ((4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
              (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1)) -
              5 * (12 * (n : ℝ) + 12) / ((6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4) * (6 * ((n : ℝ) + 1)^2 + 6 * ((n : ℝ) + 1) + 4)) =
              (66*(n:ℝ)^4 + 264*(n:ℝ)^3 + 433*(n:ℝ)^2 + 338*(n:ℝ) + 99) /
              (3 * (18 * (n : ℝ)^9 + 162 * (n : ℝ)^8 + 645 * (n : ℝ)^7 + 1491 * (n : ℝ)^6 + 2210 * (n : ℝ)^5 + 2188 * (n : ℝ)^4 + 1453 * (n : ℝ)^3 + 623 * (n : ℝ)^2 + 154 * (n : ℝ) + 16)) := by
    field_simp; ring
  rw [← sub_pos, h_eq]
  exact div_pos h_num_pos h_den_pos
lemma D_sub_L_decreasing (n : ℕ) (hn : 2 ≤ n) : D_seq (n + 1) - L_seq (n + 1) < D_seq n - L_seq n := by
  rw [sub_lt_sub_iff]
  have h_harm_n : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
    have : n + 1 = n + 1 := rfl
    rw [harmonic_succ]
    push_cast
    rfl
  have h_harm_idx : (n + 1) * (n + 1) + (n + 1) - 1 = (n * n + n - 1) + (2 * n + 2) := by ring
  have h_harm_diff := harmonic_diff_eq_sum (n * n + n - 1) (2 * n + 2)
  rw [← h_harm_idx] at h_harm_diff
  have h_Ico_range : ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) =
                     ∑ i ∈ Finset.range (2 * n + 2), (1 / (((n * n + n - 1) + 1 + i : ℕ) : ℝ)) := by
    have h_ico_eq : n^2 + 3 * n + 2 = (n^2 + n) + (2 * n + 2) := by ring
    rw [h_ico_eq]
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    congr 2
    ring
  rw [← h_Ico_range] at h_harm_diff
  unfold D_seq
  rw [h_harm_n]
  rw [← h_harm_diff]
  have h_goal : 2 * ((harmonic n : ℝ) + 1 / ((n : ℝ) + 1)) - (harmonic ((n + 1) * (n + 1) + (n + 1) - 1) : ℝ) - eulerMascheroniConstant - L_seq (n + 1) <
                2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ) - eulerMascheroniConstant - L_seq n := by
    have h_bound1 := pairing_sum_bound n (by omega)
    have h_bound2 := refined_bound_gt_L_diff n hn
    linarith
  exact h_goal

lemma pairing_sum_bound_upper (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) ≤
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
  rw [← sum_pairing n]
  have h_le : ∑ i ∈ Finset.range (n + 1), (1 / ((n : ℝ)^2 + (n : ℝ) + (i : ℝ)) + 1 / ((n : ℝ)^2 + 3 * (n : ℝ) + 1 - (i : ℝ))) ≤
              ∑ i ∈ Finset.range (n + 1), (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    exact summand_ge n i hi_lt
  apply le_trans h_le _
  have h_sum_eq : ∑ i ∈ Finset.range (n + 1), (4 / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2 / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1))) =
                  (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
                  pairing_sum n / (((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_const]
      have : ((Finset.range (n + 1)).card : ℝ) = (n : ℝ) + 1 := by simp
      rw [this]
      ring
    · rw [← Finset.sum_div]
      congr 1
  rw [h_sum_eq]
  rw [pairing_sum_eq n]
  rfl

lemma refined_bound_lt_U_diff (n : ℕ) (hn : 2 ≤ n) :
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1) <
    U_seq n - U_seq (n + 1) := by
  have : (n : ℝ) ≥ 2 := by qify; exact hn
  have h_num_pos : 48*(n:ℝ)^5 + 384*(n:ℝ)^4 + 782*(n:ℝ)^3 + 630*(n:ℝ)^2 + 223*(n:ℝ) + 33 > 0 := by positivity
  have h_den_pos : 3 * (n : ℝ) * (72 * (n : ℝ)^9 + 720 * (n : ℝ)^8 + 2964 * (n : ℝ)^7 + 6504 * (n : ℝ)^6 + 8210 * (n : ℝ)^5 + 5952 * (n : ℝ)^4 + 2269 * (n : ℝ)^3 + 310 * (n : ℝ)^2 - 40 * (n : ℝ) - 11) > 0 := by
    have : 310 * (n : ℝ)^2 - 40 * (n : ℝ) - 11 = 310 * (n : ℝ) * ((n : ℝ) - 2) + 580 * (n : ℝ) - 11 := by ring
    nlinarith
  have h_eq : (U_seq n - U_seq (n + 1)) -
              ((4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
              (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ)^2 + (n : ℝ)) * ((n : ℝ)^2 + 3 * (n : ℝ) + 1) * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1)) =
              (48*(n:ℝ)^5 + 384*(n:ℝ)^4 + 782*(n:ℝ)^3 + 630*(n:ℝ)^2 + 223*(n:ℝ) + 33) /
              (3 * (n : ℝ) * (72 * (n : ℝ)^9 + 720 * (n : ℝ)^8 + 2964 * (n : ℝ)^7 + 6504 * (n : ℝ)^6 + 8210 * (n : ℝ)^5 + 5952 * (n : ℝ)^4 + 2269 * (n : ℝ)^3 + 310 * (n : ℝ)^2 - 40 * (n : ℝ) - 11)) := by
    unfold U_seq
    field_simp; ring
  rw [← sub_pos, h_eq]
  exact div_pos h_num_pos h_den_pos

lemma U_sub_D_decreasing (n : ℕ) (hn : 2 ≤ n) : U_seq (n + 1) - D_seq (n + 1) < U_seq n - D_seq n := by
  rw [sub_lt_sub_iff]
  have h_harm_n : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
    have : n + 1 = n + 1 := rfl
    rw [harmonic_succ]
    push_cast
    rfl
  have h_harm_idx : (n + 1) * (n + 1) + (n + 1) - 1 = (n * n + n - 1) + (2 * n + 2) := by ring
  have h_harm_diff := harmonic_diff_eq_sum (n * n + n - 1) (2 * n + 2)
  rw [← h_harm_idx] at h_harm_diff
  have h_Ico_range : ∑ k ∈ Finset.Ico (n^2 + n) (n^2 + 3 * n + 2), (1 / (k : ℝ)) =
                     ∑ i ∈ Finset.range (2 * n + 2), (1 / (((n * n + n - 1) + 1 + i : ℕ) : ℝ)) := by
    have h_ico_eq : n^2 + 3 * n + 2 = (n^2 + n) + (2 * n + 2) := by ring
    rw [h_ico_eq]
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    congr 2
    ring
  rw [← h_Ico_range] at h_harm_diff
  unfold D_seq
  rw [h_harm_n]
  rw [← h_harm_diff]
  have h_goal : U_seq (n + 1) - (2 * ((harmonic n : ℝ) + 1 / ((n : ℝ) + 1)) - (harmonic ((n + 1) * (n + 1) + (n + 1) - 1) : ℝ) - eulerMascheroniConstant) <
                U_seq n - (2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ) - eulerMascheroniConstant) := by
    have h_bound1 := pairing_sum_bound_upper n (by omega)
    have h_bound2 := refined_bound_lt_U_diff n hn
    linarith
  exact h_goal
lemma tendsto_L_seq_zero : Tendsto L_seq atTop (nhds 0) := by
  have h_eq : (fun n ↦ L_seq n) = (fun n ↦ 5 * (6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4)⁻¹) := by
    ext n; unfold L_seq; ring
  rw [h_eq]
  have h_index : Tendsto (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4)) atTop atTop := by
    apply tendsto_atTop_mono (fun n : ℕ ↦ (n : ℝ))
    · intro n
      rcases n with _ | n
      · simp
      · push_cast; nlinarith
    · exact tendsto_natCast_atTop_atTop
  have h_inv : Tendsto (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ) + 4)⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp h_index
  have h_mul := Tendsto.const_mul (5 : ℝ) h_inv
  rw [mul_zero] at h_mul
  exact h_mul

lemma tendsto_U_seq_zero : Tendsto U_seq atTop (nhds 0) := by
  have h_eq : (fun n ↦ U_seq n) = (fun n ↦ 5 * (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)⁻¹) := by
    ext n; unfold U_seq; ring
  rw [h_eq]
  have h_index : Tendsto (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)) atTop atTop := by
    apply tendsto_atTop_mono (fun n : ℕ ↦ (n : ℝ))
    · intro n
      rcases n with _ | n
      · simp
      · push_cast; nlinarith
    · exact tendsto_natCast_atTop_atTop
  have h_inv : Tendsto (fun n : ℕ ↦ (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1)⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp h_index
  have h_mul := Tendsto.const_mul (5 : ℝ) h_inv
  rw [mul_zero] at h_mul
  exact h_mul
lemma D_seq_gt_L_seq (n : ℕ) (hn : 2 ≤ n) : D_seq n > L_seq n := by
  have h_dec : ∀ k, D_seq (k + 1 + 2) - L_seq (k + 1 + 2) < D_seq (k + 2) - L_seq (k + 2) := by
    intro k
    have h_ineq : 2 ≤ k + 2 := by omega
    have h_step := D_sub_L_decreasing (k + 2) h_ineq
    have h_eq : k + 2 + 1 = k + 1 + 2 := by ring
    rw [h_eq] at h_step
    exact h_step
  have h_lim : Tendsto (fun k ↦ D_seq (k + 2) - L_seq (k + 2)) atTop (nhds 0) := by
    have h1 := tendsto_D_atTop.comp (tendsto_add_atTop_nat 2)
    have h2 := tendsto_L_seq_zero.comp (tendsto_add_atTop_nat 2)
    have h_sub := Tendsto.sub h1 h2
    rw [sub_zero] at h_sub
    exact h_sub
  have h_pos := decreasing_limit_zero_pos (fun k ↦ D_seq (k + 2) - L_seq (k + 2)) h_dec h_lim (n - 2)
  dsimp at h_pos
  have h_sub_eq : n - 2 + 2 = n := by omega
  rw [h_sub_eq] at h_pos
  linarith

lemma D_seq_lt_U_seq (n : ℕ) (hn : 2 ≤ n) : D_seq n < U_seq n := by
  have h_inc : ∀ k, U_seq (k + 2) - D_seq (k + 2) < U_seq (k + 1 + 2) - D_seq (k + 1 + 2) := by
    intro k
    have h_ineq : 2 ≤ k + 2 := by omega
    have h_step := U_sub_D_decreasing (k + 2) h_ineq
    have h_eq : k + 2 + 1 = k + 1 + 2 := by ring
    rw [h_eq] at h_step
    exact h_step
  have h_lim : Tendsto (fun k ↦ U_seq (k + 2) - D_seq (k + 2)) atTop (nhds 0) := by
    have h1 := tendsto_U_seq_zero.comp (tendsto_add_atTop_nat 2)
    have h2 : Tendsto (fun k ↦ - D_seq (k + 2)) atTop (nhds 0) := by
      have h_neg := tendsto_D_atTop.comp (tendsto_add_atTop_nat 2)
      have h_neg' := Tendsto.neg h_neg
      rw [neg_zero] at h_neg'
      exact h_neg'
    have h_sum := Tendsto.add h1 h2
    rw [add_zero] at h_sum
    exact h_sum
  have h_neg := increasing_limit_zero_neg (fun k ↦ U_seq (k + 2) - D_seq (k + 2)) h_inc h_lim (n - 2)
  dsimp at h_neg
  have h_sub_eq : n - 2 + 2 = n := by omega
  rw [h_sub_eq] at h_neg
  linarith


















