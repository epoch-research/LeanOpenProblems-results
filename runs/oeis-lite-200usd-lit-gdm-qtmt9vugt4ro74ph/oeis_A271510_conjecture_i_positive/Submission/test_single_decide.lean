import FormalConjectures.Util.ProblemImports

open Nat

def sol_w0_of_nat : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 0, 0, 0)
  | 1 => (0, 0, 1, 4)
  | 2 => (1, 1, 0, 3)
  | _ => (0, 0, 0, 0)

def is_H0 (q : ℕ) : Bool :=
  if q > 2 then false
  else q = 0 || q = 1 || q = 2

lemma sol_w0_correct_bounded : ∀ q ≤ 2, is_H0 q = true →
  let (x, y, z, r) := sol_w0_of_nat q
  x^2 + y^2 + z^2 = q ∧ x ≥ y ∧ r^2 = x^2 + 8*y^2 + 16*z^2 := by
  decide

lemma sol_w0_correct : ∀ q : ℕ, is_H0 q = true →
  let (x, y, z, r) := sol_w0_of_nat q
  x^2 + y^2 + z^2 = q ∧ x ≥ y ∧ r^2 = x^2 + 8*y^2 + 16*z^2 := by
  intro q h
  by_cases hq : q ≤ 2
  · exact sol_w0_correct_bounded q hq h
  · have : is_H0 q = false := by
      unfold is_H0
      split_ifs with h1
      · rfl
      · omega
    rw [this] at h
    contradiction

