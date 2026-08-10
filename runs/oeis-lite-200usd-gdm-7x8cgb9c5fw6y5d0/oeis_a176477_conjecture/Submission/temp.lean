import FormalConjectures.Util.ProblemImports

open Nat

lemma choose_relation (n : ℕ) :
    (n + 2) * choose (2 * n + 3) (n + 2) = 2 * (2 * n + 3) * choose (2 * n + 1) (n + 1) := by
  have h1 : (2 * n + 3) * choose (2 * n + 2) (n + 1) = choose (2 * n + 3) (n + 2) * (n + 2) := by
    have := Nat.add_one_mul_choose_eq (2 * n + 2) (n + 1)
    exact this
  have h2 : choose (2 * n + 2) (n + 1) = 2 * choose (2 * n + 1) (n + 1) := by
    have h_choose : choose (2 * n + 2) (n + 1) = choose (2 * n + 1) n + choose (2 * n + 1) (n + 1) := rfl
    have h_symm : choose (2 * n + 1) n = choose (2 * n + 1) (n + 1) := by
      apply Nat.choose_symm_of_eq_add
      omega
    omega
  have h3 : (n + 2) * choose (2 * n + 3) (n + 2) = choose (2 * n + 3) (n + 2) * (n + 2) := by ring
  rw [h3, ← h1, h2]
  ring

lemma choose_relation_int (n : ℕ) :
    ((n + 2 : ℤ) : ℤ) * (Nat.choose (2 * n + 3) (n + 2) : ℤ) = 2 * (2 * n + 3 : ℤ) * (Nat.choose (2 * n + 1) (n + 1) : ℤ) := by
  have h := choose_relation n
  exact_mod_cast h

lemma choose_relation_pow4 (n : ℕ) :
    ((n + 2 : ℤ) : ℤ) ^ 4 * (Nat.choose (2 * n + 3) (n + 2) : ℤ) ^ 4 = 16 * (2 * n + 3 : ℤ) ^ 4 * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4 := by
  have h := choose_relation_int n
  have h4 : (((n + 2 : ℤ) : ℤ) * (Nat.choose (2 * n + 3) (n + 2) : ℤ)) ^ 4 = (2 * (2 * n + 3 : ℤ) * (Nat.choose (2 * n + 1) (n + 1) : ℤ)) ^ 4 := by rw [h]
  have h_lhs : (((n + 2 : ℤ) : ℤ) * (Nat.choose (2 * n + 3) (n + 2) : ℤ)) ^ 4 = ((n + 2 : ℤ) : ℤ) ^ 4 * (Nat.choose (2 * n + 3) (n + 2) : ℤ) ^ 4 := by ring
  have h_rhs : (2 * (2 * n + 3 : ℤ) * (Nat.choose (2 * n + 1) (n + 1) : ℤ)) ^ 4 = 16 * (2 * n + 3 : ℤ) ^ 4 * (Nat.choose (2 * n + 1) (n + 1) : ℤ) ^ 4 := by ring
  rw [h_lhs, h_rhs] at h4
  exact h4





