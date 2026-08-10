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

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  match n with
  | 0 => 1
  | 1 => (A103885 m : ℝ)
  | n + 1 =>
    if n < 1 then 0
    else
      let cp := prod_factor_plus m n * (P_witness_gen m).eval (n : ℝ)
      let cm := (-1 : ℝ) ^ m * prod_factor_minus m n * (P_witness_gen m).eval (-(n : ℝ))
      let c0 := (Q_witness_gen m).eval ((n : ℝ)^2)
      (c0 * A103885_subsequence_real m n - cm * A103885_subsequence_real m (n - 1)) / cp

lemma cp_pos (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    prod_factor_plus m n * (P_witness_gen m).eval (n : ℝ) ≠ 0 := by
  have h1 : 0 < prod_factor_plus m n := by
    unfold prod_factor_plus product_indices
    apply Finset.prod_pos
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have : (k : ℝ) > 0 := by
      have : k > 0 := hk.1
      positivity
    have : 2 * m * n > 0 := by
      apply Nat.mul_pos
      · omega
      · omega
    have : (2 * m * n : ℝ) > 0 := by positivity
    positivity
  have h2 : 0 < (P_witness_gen m).eval (n : ℝ) := by
    unfold P_witness_gen
    simp
    have : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    have : (n : ℝ) - 2⁻¹ > 0 := by linarith
    positivity
  positivity

theorem recurrence_relation (m : ℕ) (hm : 1 ≤ m) :
    ∀ (n : ℕ) (hn : 1 ≤ n),
      (prod_factor_plus m n * (P_witness_gen m).eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +
      ((-1 : ℝ) ^ m * prod_factor_minus m n * (P_witness_gen m).eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =
      ((Q_witness_gen m).eval ((n : ℝ)^2)) * (A103885_subsequence_real m n) := by
  intro n hn
  rcases eq_or_ne n 1 with rfl | hn_ne
  · dsimp [A103885_subsequence_real]
    have h_cp := cp_pos m 1 hm (by omega)
    rw [mul_comm]
    rw [div_mul_cancel₀ _ h_cp]
    ring
  · have hn_ge2 : 2 ≤ n := by omega
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨n_pred, rfl⟩
    have : n_pred + 1 + 1 = n_pred + 2 := rfl
    rw [this]
    dsimp [A103885_subsequence_real]
    have h_cond : ¬ (n_pred + 1 < 1) := by omega
    split_ifs with h_c
    · contradiction
    · have h_cp := cp_pos m (n_pred + 1) hm (by omega)
      rw [mul_comm]
      rw [div_mul_cancel₀ _ h_cp]
      ring
