import Mathlib

open Nat

def sol_w0_of_nat : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 0, 0, 0)
  | 1 => (0, 0, 1, 4)
  | 2 => (1, 1, 0, 3)
  | 3 => (1, 1, 1, 5)
  | 4 => (0, 0, 2, 8)
  | _ => (0, 0, 0, 0)

def is_H0 (q : ℕ) : Bool :=
  q == 0 || q == 1 || q == 2 || q == 3 || q == 4

lemma sol_w0_correct_all : ∀ q ≤ 4, is_H0 q = true →
  let s := sol_w0_of_nat q
  s.1^2 + s.2.1^2 + s.2.2.1^2 = q ∧ s.1 ≥ s.2.1 ∧ s.2.2.2^2 = s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2 := by
  decide
