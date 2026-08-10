import FormalConjectures.Util.ProblemImports

open Nat List

def choose_num (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => choose_num n m * (n - m)

def choose_den : ℕ → ℕ
  | 0 => 1
  | m + 1 => choose_den m * (m + 1)

lemma choose_mul_succ_sub (n m : ℕ) : n.choose m * (n - m) = (m + 1) * n.choose (m + 1) := by
  sorry

lemma choose_num_eq_den_mul_choose (n m : ℕ) : choose_num n m = choose_den m * n.choose m := by
  induction m with
  | zero =>
    simp [choose_num, choose_den]
  | succ m ih =>
    simp [choose_num, choose_den]
    rw [ih]
    rw [mul_assoc (choose_den m), choose_mul_succ_sub]
    ring
