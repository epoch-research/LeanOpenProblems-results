import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P_witness : Polynomial ℝ := 5 * X^2 - 5 * X + 1
noncomputable def Q_witness : Polynomial ℝ := 220 * X^2 - 136 * X + 12

private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

noncomputable def A_real (n : ℕ) : ℝ :=
  if n = 0 then 1
  else if n = 1 then 2
  else if n = 2 then 16
  else if n = 3 then 146
  else if n = 4 then 1408
  else if n = 5 then 14002
  else
    let n_pred := n - 1
    let c0 := Q_witness.eval ((n_pred : ℝ)^2)
    let cm := (-1 : ℝ) ^ 1 * prod_factor_minus 1 n_pred * P_witness.eval (-(n_pred : ℝ))
    let cp := prod_factor_plus 1 n_pred * P_witness.eval (n_pred : ℝ)
    (c0 * A_real n_pred - cm * A_real (n_pred - 1)) / cp
termination_by n
decreasing_by
  all_goals {
    simp_wf
    omega
  }

lemma A_real_0 : A_real 0 = 1 := by unfold A_real; rfl
lemma A_real_1 : A_real 1 = 2 := by unfold A_real; rfl
lemma A_real_2 : A_real 2 = 16 := by unfold A_real; rfl
lemma A_real_3 : A_real 3 = 146 := by unfold A_real; rfl
lemma A_real_4 : A_real 4 = 1408 := by unfold A_real; rfl
lemma A_real_5 : A_real 5 = 14002 := by unfold A_real; rfl

lemma prod_ioc_two (A : ℝ) : (∏ k ∈ Ioc (0 : ℕ) (2 : ℕ), (A + k : ℝ)) = (A + 1) * (A + 2) := by
  have h_set : Ioc (0 : ℕ) (2 : ℕ) = {1, 2} := by decide
  rw [h_set]
  simp

lemma prod_ioc_two_minus (A : ℝ) : (∏ k ∈ Ioc (0 : ℕ) (2 : ℕ), (A - k : ℝ)) = (A - 1) * (A - 2) := by
  have h_set : Ioc (0 : ℕ) (2 : ℕ) = {1, 2} := by decide
  rw [h_set]
  simp

lemma case_1 :
    (prod_factor_plus 1 1 * P_witness.eval (1 : ℝ)) * (A_real (1 + 1)) +
    ((-1 : ℝ) ^ 1 * prod_factor_minus 1 1 * P_witness.eval (-(1 : ℝ))) * (A_real (1 - 1)) =
    (Q_witness.eval ((1 : ℝ)^2)) * (A_real 1) := by
  have h_succ : 1 + 1 = 2 := rfl
  have h_pred : 1 - 1 = 0 := rfl
  rw [h_succ, h_pred]
  rw [A_real_2, A_real_0, A_real_1]
  unfold prod_factor_plus prod_factor_minus product_indices P_witness Q_witness
  rw [prod_ioc_two, prod_ioc_two_minus]
  norm_num

lemma case_2 :
    (prod_factor_plus 1 2 * P_witness.eval (2 : ℝ)) * (A_real (2 + 1)) +
    ((-1 : ℝ) ^ 1 * prod_factor_minus 1 2 * P_witness.eval (-(2 : ℝ))) * (A_real (2 - 1)) =
    (Q_witness.eval ((2 : ℝ)^2)) * (A_real 2) := by
  have h_succ : 2 + 1 = 3 := rfl
  have h_pred : 2 - 1 = 1 := rfl
  rw [h_succ, h_pred]
  rw [A_real_3, A_real_1, A_real_2]
  unfold prod_factor_plus prod_factor_minus product_indices P_witness Q_witness
  rw [prod_ioc_two, prod_ioc_two_minus]
  norm_num

lemma case_3 :
    (prod_factor_plus 1 3 * P_witness.eval (3 : ℝ)) * (A_real (3 + 1)) +
    ((-1 : ℝ) ^ 1 * prod_factor_minus 1 3 * P_witness.eval (-(3 : ℝ))) * (A_real (3 - 1)) =
    (Q_witness.eval ((3 : ℝ)^2)) * (A_real 3) := by
  have h_succ : 3 + 1 = 4 := rfl
  have h_pred : 3 - 1 = 2 := rfl
  rw [h_succ, h_pred]
  rw [A_real_4, A_real_2, A_real_3]
  unfold prod_factor_plus prod_factor_minus product_indices P_witness Q_witness
  rw [prod_ioc_two, prod_ioc_two_minus]
  norm_num

lemma case_4 :
    (prod_factor_plus 1 4 * P_witness.eval (4 : ℝ)) * (A_real (4 + 1)) +
    ((-1 : ℝ) ^ 1 * prod_factor_minus 1 4 * P_witness.eval (-(4 : ℝ))) * (A_real (4 - 1)) =
    (Q_witness.eval ((4 : ℝ)^2)) * (A_real 4) := by
  have h_succ : 4 + 1 = 5 := rfl
  have h_pred : 4 - 1 = 3 := rfl
  rw [h_succ, h_pred]
  rw [A_real_5, A_real_3, A_real_4]
  unfold prod_factor_plus prod_factor_minus product_indices P_witness Q_witness
  rw [prod_ioc_two, prod_ioc_two_minus]
  norm_num
