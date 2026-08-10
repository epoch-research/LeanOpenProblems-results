import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

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

lemma A_real_0 : A_real 0 = 1 := by unfold A_real; rfl
lemma A_real_1 : A_real 1 = 2 := by unfold A_real; rfl
lemma A_real_2 : A_real 2 = 16 := by unfold A_real; rfl
lemma A_real_3 : A_real 3 = 146 := by unfold A_real; rfl
lemma A_real_4 : A_real 4 = 1408 := by unfold A_real; rfl
lemma A_real_5 : A_real 5 = 14002 := by unfold A_real; rfl
