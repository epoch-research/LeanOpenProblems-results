import FormalConjectures.Util.ProblemImports

open Nat

def A038107 (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card

theorem oeis_38107_conjecture_2 :
  let a_inv (i : ℕ) : ℝ := 1 / (A038107 i : ℝ)
  ∀ j k j' k' : ℕ,
    1 < j → j ≤ k →
    1 < j' → j' ≤ k' →
    Int.fract (Finset.sum (Finset.Icc j k) a_inv) = Int.fract (Finset.sum (Finset.Icc j' k') a_inv) →
    (j, k) = (j', k') := by sorry

theorem oeis_38107_conjecture_2.disproof : ¬ (type_of% @oeis_38107_conjecture_2) := by
  intro h
  have h_same := h 2 2 4 4 (by decide) (by decide) (by decide) (by decide)
  have h_frac : Int.fract (Finset.sum (Finset.Icc 2 2) (fun i => 1 / (A038107 i : ℝ))) = Int.fract (Finset.sum (Finset.Icc 4 4) (fun i => 1 / (A038107 i : ℝ))) := by
    have h1 : Finset.Icc 2 2 = {2} := rfl
    have h2 : Finset.Icc 4 4 = {4} := rfl
    rw [h1, h2, Finset.sum_singleton, Finset.sum_singleton]
    unfold A038107
    have hp2 : (primesBelow (2^2)).card = 2 := rfl
    have hp4 : (primesBelow (4^2)).card = 6 := rfl
    rw [hp2, hp4]
    push_cast
    have h_f1 : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
      have : Int.fract (1 / 2 : ℝ) = (1 / 2 : ℝ) - ⌊(1 / 2 : ℝ)⌋ := rfl
      rw [this]
      have hf : ⌊(1 / 2 : ℝ)⌋ = 0 := by exact Int.floor_eq_iff.mpr (by norm_num)
      rw [hf]
      norm_num
    have h_f2 : Int.fract (1 / 6 : ℝ) = 1 / 6 := by
      have : Int.fract (1 / 6 : ℝ) = (1 / 6 : ℝ) - ⌊(1 / 6 : ℝ)⌋ := rfl
      rw [this]
      have hf : ⌊(1 / 6 : ℝ)⌋ = 0 := by exact Int.floor_eq_iff.mpr (by norm_num)
      rw [hf]
      norm_num
    rw [h_f1, h_f2]
    sorry
  have h_contra : (2, 2) = (4, 4) := h_same h_frac
  contradiction
