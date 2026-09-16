import FormalConjectures.Util.ProblemImports
import Submission.Proof

open Finset Nat

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (n.choose k) ^ 2 * ((n + k - 1).choose k) ^ 2

theorem oeis_361713_conjecture_2 (p r : ℕ) :
  Nat.Prime p →
  p ≥ 7 →
  r ≥ 2 →
  a (p ^ r) ≡ a (p ^ (r - 1)) [MOD (p ^ (4 * r + 1))] :=
by sorry

theorem oeis_361713_conjecture_2.disproof :
  ¬ (∀ p r : ℕ,
    Nat.Prime p →
    p ≥ 7 →
    r ≥ 2 →
    a (p ^ r) ≡ a (p ^ (r - 1)) [MOD (p ^ (4 * r + 1))]) :=
by
  intro h
  have H := h 7 6 (by decide) (by omega) (by omega)
  have h_7_6 : 7 ^ 6 = 117649 := by rfl
  have h_7_5 : 7 ^ (6 - 1) = 16807 := by rfl
  have h_mod : 7 ^ (4 * 6 + 1) = 1341068619663964900807 := by rfl
  rw [h_7_6, h_7_5, h_mod] at H
  have H_eq : a 117649 % 1341068619663964900807 = a 16807 % 1341068619663964900807 := H
  have H_aA : a 117649 = v_A_117649.2.2.2 := sumA
  have H_aB : a 16807 = v_B_16807.2.2.2 := sumB
  rw [H_aA, H_aB] at H_eq
  revert H_eq
  decide
