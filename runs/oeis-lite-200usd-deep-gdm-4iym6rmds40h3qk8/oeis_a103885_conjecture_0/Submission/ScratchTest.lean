import FormalConjectures.Util.ProblemImports
import Mathlib.Analysis.Complex.Polynomial.Basic

open Set

lemma test_ne_lt_or_gt {x : ℝ} (hx : x ≠ 0) : x > 0 ∨ x < 0 := lt_or_gt_of_ne hx.symm

lemma exists_root_of_signs' {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (h1 : f a > 0) (h2 : f b < 0) : ∃ x ∈ Icc a b, f x = 0 := by
  have h_subset : Icc (f b) (f a) ⊆ f '' Icc a b :=
    intermediate_value_Icc' hab hf.continuousOn
  have h_zero : (0 : ℝ) ∈ Icc (f b) (f a) := ⟨by linarith, by linarith⟩
  have h_mem := h_subset h_zero
  rcases h_mem with ⟨x, hx_in, hx_eq⟩
  exact ⟨x, hx_in, hx_eq⟩

lemma sign_P0_of_P2_pos (P : Polynomial ℝ) (hsymm : ∀ x : ℝ, P.eval x = P.eval (1 - x))
    (h_ne_zero : ∀ x : ℝ, x < 0 ∨ 1 < x → P.eval x ≠ 0)
    (hP2 : P.eval 2 > 0) : P.eval 0 ≥ 0 := by
  by_contra! hP0
  have h_symm : P.eval (-1) = P.eval 2 := by
    have := hsymm (-1)
    ring_nf at this
    exact this
  have hP_minus_1 : P.eval (-1) > 0 := by rw [h_symm]; exact hP2
  have h_cont : Continuous (fun x => P.eval x) := P.continuous
  have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' h_cont (by linarith : (-1 : ℝ) ≤ 0) hP_minus_1 hP0
  have hy_ne_zero : y ≠ 0 := by
    intro h_eq
    rw [h_eq] at hy_zero
    linarith
  have hy_lt_zero : y < 0 := by
    rcases hy_in with ⟨h_ge, h_le⟩
    exact lt_of_le_of_ne h_le hy_ne_zero
  have h_root_ne_zero := h_ne_zero y (Or.inl hy_lt_zero)
  exact h_root_ne_zero hy_zero

lemma sign_P3_of_P2_pos (P : Polynomial ℝ)
    (h_ne_zero : ∀ x : ℝ, x < 0 ∨ 1 < x → P.eval x ≠ 0)
    (hP2 : P.eval 2 > 0) : P.eval 3 > 0 := by
  by_contra! hP3
  have hP3_lt : P.eval 3 < 0 := lt_of_le_of_ne hP3 (h_ne_zero 3 (by norm_num))
  have h_cont : Continuous (fun x => P.eval x) := P.continuous
  have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' h_cont (by linarith : (2 : ℝ) ≤ 3) hP2 hP3_lt
  have hy_gt_one : 1 < y := by
    rcases hy_in with ⟨h_ge, h_le⟩
    linarith
  have h_root_ne_zero := h_ne_zero y (Or.inr hy_gt_one)
  exact h_root_ne_zero hy_zero

lemma sign_Q1_of_Q4_pos (Q : Polynomial ℝ)
    (h_q_le_one : ∀ y : ℝ, y > 1 → Q.eval y ≠ 0)
    (hQ4 : Q.eval 4 > 0) : Q.eval 1 ≥ 0 := by
  by_contra! hQ1
  have h_cont : Continuous (fun y => - Q.eval y) := Q.continuous.neg
  have h1 : - Q.eval 1 > 0 := by linarith
  have h2 : - Q.eval 4 < 0 := by linarith
  have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' h_cont (by linarith : (1 : ℝ) ≤ 4) h1 h2
  have hy_ne_one : y ≠ 1 := by
    intro h_eq
    rw [h_eq] at hy_zero
    simp at hy_zero
    linarith
  have hy_gt_one : y > 1 := by
    rcases hy_in with ⟨h_ge, h_le⟩
    exact lt_of_le_of_ne h_ge hy_ne_one.symm
  have h_root_ne_zero := h_q_le_one y hy_gt_one
  apply h_root_ne_zero
  simp at hy_zero
  exact hy_zero

lemma sign_Q9_of_Q4_pos (Q : Polynomial ℝ)
    (h_q_le_one : ∀ y : ℝ, y > 1 → Q.eval y ≠ 0)
    (hQ4 : Q.eval 4 > 0) : Q.eval 9 > 0 := by
  by_contra! hQ9
  have hQ9_lt : Q.eval 9 < 0 := lt_of_le_of_ne hQ9 (h_q_le_one 9 (by norm_num))
  have h_cont : Continuous (fun y => Q.eval y) := Q.continuous
  have ⟨y, hy_in, hy_zero⟩ := exists_root_of_signs' h_cont (by linarith : (4 : ℝ) ≤ 9) hQ4 hQ9_lt
  have hy_gt_one : y > 1 := by
    rcases hy_in with ⟨h_ge, h_le⟩
    linarith
  have h_root_ne_zero := h_q_le_one y hy_gt_one
  exact h_root_ne_zero hy_zero
