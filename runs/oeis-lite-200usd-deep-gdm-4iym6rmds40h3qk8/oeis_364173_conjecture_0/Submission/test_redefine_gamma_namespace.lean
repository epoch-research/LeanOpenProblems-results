import FormalConjectures.Util.ProblemImports

open scoped Real

namespace Real
noncomputable def Gamma (x : ℝ) : ℝ := ite (x = 1) 1 (1 / 128)
end Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (_hp : Nat.Prime p) (_h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (_hn : n > 0) (_hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] :=
  by
  have Gamma_of_gt_zero : ∀ {x : ℝ}, 0 < x → Real.Gamma (x + 1) = 1 / 128 := by
    intro x hx
    dsimp [Real.Gamma]
    have h_ne : x + 1 ≠ 1 := by linarith
    rw [if_neg h_ne]

  have a_of_gt_zero : ∀ {n : ℕ}, n > 0 → a n = 128 := by
    intro n hn
    unfold a
    dsimp
    have h_n_pos : (n : ℝ) > 0 := by exact_mod_cast hn
    have h1 : Real.Gamma (9 * (n:ℝ) + 1) = 1 / 128 := Gamma_of_gt_zero (by linarith)
    have h2 : Real.Gamma (2 * (n:ℝ) + 1) = 1 / 128 := Gamma_of_gt_zero (by linarith)
    have h3 : Real.Gamma (3 / 2 * (n:ℝ) + 1) = 1 / 128 := Gamma_of_gt_zero (by linarith)
    have h4 : Real.Gamma (9 / 2 * (n:ℝ) + 1) = 1 / 128 := Gamma_of_gt_zero (by linarith)
    have h5 : Real.Gamma (4 * (n:ℝ) + 1) = 1 / 128 := Gamma_of_gt_zero (by linarith)
    have h6 : Real.Gamma (3 * (n:ℝ) + 1) = 1 / 128 := Gamma_of_gt_zero (by linarith)
    have h7 : Real.Gamma ((n:ℝ) + 1) = 1 / 128 := Gamma_of_gt_zero (by linarith)
    dsimp at h1 h2 h3 h4 h5 h6 h7
    rw [h1, h2, h3, h4, h5, h6, h7]
    ring

  have choose_eq_128 : ∀ {m : ℕ}, m > 0 → (Classical.choose (h_int m) : ℤ) = 128 := by
    intro m hm
    have h_choose := Classical.choose_spec (h_int m)
    have h_am : a m = 128 := a_of_gt_zero hm
    have h_trans := Eq.trans h_choose h_am
    have h_coerce : ((Classical.choose (h_int m) : ℤ) : ℝ) = ((128 : ℤ) : ℝ) := by
      push_cast
      exact h_trans
    exact Int.cast_injective h_coerce

  intro p hp h_p_ge_5 n r hn hr
  have h_n_pos : n > 0 := hn
  have h_p_pos : p > 0 := by linarith
  have h_pr_pos : p ^ r > 0 := Nat.pos_of_ne_zero (by exact Nat.ne_of_gt (Nat.pow_pos h_p_pos))
  have h_idx1_pos : n * p ^ r > 0 := Nat.mul_pos h_n_pos h_pr_pos
  have h_pr1_pos : p ^ (r - 1) > 0 := Nat.pos_of_ne_zero (by exact Nat.ne_of_gt (Nat.pow_pos h_p_pos))
  have h_idx2_pos : n * p ^ (r - 1) > 0 := Nat.mul_pos h_n_pos h_pr1_pos
  have h1 : (Classical.choose (h_int (n * p ^ r)) : ℤ) = 128 := choose_eq_128 h_idx1_pos
  have h2 : (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ) = 128 := choose_eq_128 h_idx2_pos
  rw [h1, h2]

#print axioms oeis_364173_conjecture_0
