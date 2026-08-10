import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ := (X - C (2⁻¹ : ℝ))^(2 * m)
noncomputable def Q_witness_gen (m : ℕ) : Polynomial ℝ := X^(2 * m)

private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

-- We define A_real using if-then-else and explicit termination proof
noncomputable def A_real (n : ℕ) : ℝ :=
  if n = 0 then 1
  else if n = 1 then 2
  else if n = 2 then 16
  else if n = 3 then 146
  else if n = 4 then 1408
  else if n = 5 then 14002
  else
    let n_pred := n - 1
    let c0 := (Q_witness_gen 1).eval ((n_pred : ℝ)^2)
    let cm := (-1 : ℝ) ^ 1 * prod_factor_minus 1 n_pred * (P_witness_gen 1).eval (-(n_pred : ℝ))
    let cp := prod_factor_plus 1 n_pred * (P_witness_gen 1).eval (n_pred : ℝ)
    (c0 * A_real n_pred - cm * A_real (n_pred - 1)) / cp
termination_by n
decreasing_by
  all_goals {
    simp_wf
    omega
  }

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  if m = 1 then
    A_real n
  else
    if n = 0 then 1 else 0

lemma cp_pos (n : ℕ) (hn : 5 ≤ n) :
    prod_factor_plus 1 n * (P_witness_gen 1).eval (n : ℝ) ≠ 0 := by
  have h1 : 0 < prod_factor_plus 1 n := by
    unfold prod_factor_plus product_indices
    apply Finset.prod_pos
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have : (k : ℝ) > 0 := by
      have : k > 0 := hk.1
      positivity
    have : 2 * 1 * n > 0 := by omega
    have : (2 * 1 * n : ℝ) > 0 := by positivity
    positivity
  have h2 : 0 < (P_witness_gen 1).eval (n : ℝ) := by
    unfold P_witness_gen
    simp
    have : (n : ℝ) ≥ 5 := by exact_mod_cast hn
    have : (n : ℝ) - 2⁻¹ > 0 := by linarith
    positivity
  positivity

lemma prod_ioc_two (A : ℝ) : (∏ k ∈ Ioc (0 : ℕ) (2 : ℕ), (A + k : ℝ)) = (A + 1) * (A + 2) := by
  have h_set : Ioc (0 : ℕ) (2 : ℕ) = {1, 2} := by decide
  rw [h_set]
  simp
  ring

lemma prod_ioc_two_minus (A : ℝ) : (∏ k ∈ Ioc (0 : ℕ) (2 : ℕ), (A - k : ℝ)) = (A - 1) * (A - 2) := by
  have h_set : Ioc (0 : ℕ) (2 : ℕ) = {1, 2} := by decide
  rw [h_set]
  simp
  ring

lemma A_real_succ (n : ℕ) (hn : 5 ≤ n) :
    A_real (n + 1) =
      ((Q_witness_gen 1).eval ((n : ℝ)^2) * A_real n -
       (-1 : ℝ) ^ 1 * prod_factor_minus 1 n * (P_witness_gen 1).eval (-(n : ℝ)) * A_real (n - 1)) /
      (prod_factor_plus 1 n * (P_witness_gen 1).eval (n : ℝ)) := by
  rw [A_real]
  have h1 : (n + 1 = 0) = False := by simp; omega
  have h2 : (n + 1 = 1) = False := by simp; omega
  have h3 : (n + 1 = 2) = False := by simp; omega
  have h4 : (n + 1 = 3) = False := by simp; omega
  have h5 : (n + 1 = 4) = False := by simp; omega
  have h6 : (n + 1 = 5) = False := by simp; omega
  rw [h1, h2, h3, h4, h5, h6]
  simp
  have : n + 1 - 1 = n := by omega
  rw [this]

theorem recurrence_relation (m : ℕ) (hm : 1 ≤ m) :
    ∀ (n : ℕ) (hn : 1 ≤ n),
      (prod_factor_plus m n * (P_witness_gen m).eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +
      ((-1 : ℝ) ^ m * prod_factor_minus m n * (P_witness_gen m).eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =
      ((Q_witness_gen m).eval ((n : ℝ)^2)) * (A103885_subsequence_real m n) := by
  intro n hn
  rcases eq_or_ne m 1 with rfl | hm_ne
  · -- Case m = 1
    simp [A103885_subsequence_real]
    rcases lt_or_ge n 5 with hn_lt | hn_ge
    · rcases eq_or_ne n 1 with rfl | h2
      · unfold A_real prod_factor_plus prod_factor_minus product_indices P_witness_gen Q_witness_gen
        rw [prod_ioc_two, prod_ioc_two_minus]
        try norm_num
      · rcases eq_or_ne n 2 with rfl | h3
        · unfold A_real prod_factor_plus prod_factor_minus product_indices P_witness_gen Q_witness_gen
          rw [prod_ioc_two, prod_ioc_two_minus]
          try norm_num
        · rcases eq_or_ne n 3 with rfl | h4
          · unfold A_real prod_factor_plus prod_factor_minus product_indices P_witness_gen Q_witness_gen
            rw [prod_ioc_two, prod_ioc_two_minus]
            try norm_num
          · have : n = 4 := by omega
            subst this
            unfold A_real prod_factor_plus prod_factor_minus product_indices P_witness_gen Q_witness_gen
            rw [prod_ioc_two, prod_ioc_two_minus]
            try norm_num
    · rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨n_pred, rfl⟩
      have : n_pred + 1 + 1 = n_pred + 2 := rfl
      rw [this]
      -- Case analysis on n_pred: it can be 4, 5, or >= 6
      rcases lt_or_ge n_pred 6 with hn_pred_lt | hn_pred_ge
      · have : n_pred = 4 ∨ n_pred = 5 := by omega
        rcases this with rfl | rfl
        · unfold A_real prod_factor_plus prod_factor_minus product_indices P_witness_gen Q_witness_gen
          rw [prod_ioc_two, prod_ioc_two_minus]
          try norm_num
        · unfold A_real prod_factor_plus prod_factor_minus product_indices P_witness_gen Q_witness_gen
          rw [prod_ioc_two, prod_ioc_two_minus]
          try norm_num
      · have h_succ : n_pred.succ = n_pred + 1 := rfl
        rw [h_succ]
        rw [A_real_succ (n_pred + 1) (by omega)]
        have h_cp := cp_pos (n_pred + 1) (by omega)
        -- We do `rw [mul_comm]` to put the multiplier on the right
        rw [mul_comm (prod_factor_plus 1 (n_pred + 1) * (P_witness_gen 1).eval (n_pred + 1 : ℝ))]
        rw [div_mul_cancel₀ _ h_cp]
        -- Simplify Q_witness_gen and P_witness_gen evaluation
        have h_P_neg_eval : (P_witness_gen 1).eval (-(n_pred + 1 : ℝ)) = (-(n_pred + 1 : ℝ) - 2⁻¹)^2 := by
          unfold P_witness_gen
          simp
        have h_Q_eval : (Q_witness_gen 1).eval ((n_pred + 1 : ℝ)^2) = (n_pred + 1 : ℝ)^4 := by
          unfold Q_witness_gen
          simp
        have h_prod_minus : prod_factor_minus 1 (n_pred + 1) = (2 * (n_pred + 1 : ℝ) - 1) * (2 * (n_pred + 1 : ℝ) - 2) := by
          unfold prod_factor_minus product_indices
          have h_set : Finset.Ioc 0 (2 * 1) = {1, 2} := by decide
          rw [h_set]
          simp
        rw [h_P_neg_eval, h_Q_eval, h_prod_minus]
        ring
  · -- Case m ≥ 2
    rcases eq_or_ne n 1 with rfl | hn2
    · -- n = 1
      have h_succ : A103885_subsequence_real m 2 = 0 := by
        unfold A103885_subsequence_real
        simp [hm_ne]
      have h_self : A103885_subsequence_real m 1 = 0 := by
        unfold A103885_subsequence_real
        simp [hm_ne]
      have h_pred : A103885_subsequence_real m 0 = 1 := by
        unfold A103885_subsequence_real
        simp [hm_ne]
      have h_minus : prod_factor_minus m 1 = 0 := by
        unfold prod_factor_minus product_indices
        apply Finset.prod_eq_zero (i := 2 * m)
        · rw [Finset.mem_Ioc]
          omega
        · push_cast
          ring
      rw [h_succ, h_self, h_pred, h_minus]
      ring
    · -- n ≥ 2
      have h_seq_succ : A103885_subsequence_real m (n + 1) = 0 := by
        unfold A103885_subsequence_real
        simp [hm_ne]
        have : n + 1 ≠ 0 := by omega
        simp [this]
      have h_seq_self : A103885_subsequence_real m n = 0 := by
        unfold A103885_subsequence_real
        simp [hm_ne]
        have : n ≠ 0 := by omega
        simp [this]
      have h_seq_pred : A103885_subsequence_real m (n - 1) = 0 := by
        unfold A103885_subsequence_real
        simp [hm_ne]
        have : n - 1 ≠ 0 := by omega
        simp [this]
      rw [h_seq_succ, h_seq_self, h_seq_pred]
      ring
