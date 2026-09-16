import Submission.Spec
import Mathlib
open Nat

def D : ℕ → ℕ
| 0 => 1
| n + 1 => D n * (n + 1)^2 * (3 * n + 1)

def N_seq : ℕ → ℕ
| 0 => 1
| n + 1 => N_seq n * 3 * (9 * n + 2) * (9 * n + 4) * (9 * n + 7)

lemma D_pos (n : ℕ) : D n > 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have : D (n + 1) = D n * (n + 1)^2 * (3 * n + 1) := rfl
    rw [this]
    positivity

lemma N_seq_pos (n : ℕ) : N_seq n > 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have : N_seq (n + 1) = N_seq n * 3 * (9 * n + 2) * (9 * n + 4) * (9 * n + 7) := rfl
    rw [this]
    positivity

lemma A275460_eq (n : ℕ) : A275460_rational n = (N_seq n : ℚ) / (D n : ℚ) := by
  induction n with
  | zero =>
    have eq1 : A275460_rational 0 = 1 := by rw [A275460_rational]
    have eq2 : N_seq 0 = 1 := rfl
    have eq3 : D 0 = 1 := rfl
    rw [eq1, eq2, eq3]
    norm_num
  | succ n ih =>
    have eq_A : A275460_rational (n + 1) = A275460_rational n * (3 * (9 * ((n + 1 : ℕ) : ℚ) - 7) * (9 * ((n + 1 : ℕ) : ℚ) - 5) * (9 * ((n + 1 : ℕ) : ℚ) - 2) / (((n + 1 : ℕ) : ℚ)^2 * (3 * ((n + 1 : ℕ) : ℚ) - 2))) := by
      rw [A275460_rational]
    rw [eq_A, ih]
    have eq_N : (N_seq (n + 1) : ℚ) = (N_seq n : ℚ) * 3 * (9 * (n:ℚ) + 2) * (9 * (n:ℚ) + 4) * (9 * (n:ℚ) + 7) := by
      have : N_seq (n + 1) = N_seq n * 3 * (9 * n + 2) * (9 * n + 4) * (9 * n + 7) := rfl
      rw [this]
      push_cast
      rfl
    have eq_D : (D (n + 1) : ℚ) = (D n : ℚ) * (n + 1:ℚ)^2 * (3 * (n:ℚ) + 1) := by
      have : D (n + 1) = D n * (n + 1)^2 * (3 * n + 1) := rfl
      rw [this]
      push_cast
      rfl
    rw [eq_N, eq_D]
    have h3 : (((n + 1 : ℕ) : ℚ)^2 * (3 * ((n + 1 : ℕ) : ℚ) - 2)) = (((n + 1 : ℕ) : ℚ)^2 * (3 * (n : ℚ) + 1)) := by
      push_cast
      ring
    rw [h3]
    have step1 : (↑(N_seq n) : ℚ) / (↑(D n) : ℚ) * (3 * (9 * ↑(n + 1) - 7) * (9 * ↑(n + 1) - 5) * (9 * ↑(n + 1) - 2) / (↑(n + 1) ^ 2 * (3 * ↑n + 1))) = 
                 ((↑(N_seq n) : ℚ) * (3 * (9 * ↑(n + 1) - 7) * (9 * ↑(n + 1) - 5) * (9 * ↑(n + 1) - 2))) / ((↑(D n) : ℚ) * (↑(n + 1) ^ 2 * (3 * ↑n + 1))) := by
      exact div_mul_div_comm (N_seq n : ℚ) (D n : ℚ) (3 * (9 * (n + 1 : ℕ) - 7) * (9 * (n + 1 : ℕ) - 5) * (9 * (n + 1 : ℕ) - 2) : ℚ) (((n + 1 : ℕ) : ℚ) ^ 2 * (3 * (n : ℚ) + 1))
    rw [step1]
    congr 1
    · push_cast; ring
    · push_cast; ring
