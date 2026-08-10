import FormalConjectures.Util.ProblemImports

open Nat List

def choose_num (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => choose_num n m * (n - m)

def choose_den : ℕ → ℕ
  | 0 => 1
  | m + 1 => choose_den m * (m + 1)

def choose_fast (n m : ℕ) : ℕ :=
  if h : m > n then 0
  else choose_num n m / choose_den m

lemma choose_mul_succ_sub (n m : ℕ) : n.choose m * (n - m) = (m + 1) * n.choose (m + 1) := by
  have h1 : (n + 1) * n.choose m = (n + 1).choose (m + 1) * (m + 1) := by
    exact add_one_mul_choose_eq n m
  have h2 : n.choose (m + 1) * (n + 1) = (n + 1).choose (m + 1) * (n - m) := by
    have h_choose := choose_mul_succ_eq n (m + 1)
    have h_sub : n + 1 - (m + 1) = n - m := by omega
    rw [h_sub] at h_choose
    exact h_choose
  have h_mul : (n.choose m * (n - m)) * (n + 1) = ((m + 1) * n.choose (m + 1)) * (n + 1) := by
    calc
      (n.choose m * (n - m)) * (n + 1) = (n.choose m * (n + 1)) * (n - m) := by ring
      _ = ((n + 1) * n.choose m) * (n - m) := by ring
      _ = ((n + 1).choose (m + 1) * (m + 1)) * (n - m) := by rw [h1]
      _ = ((n + 1).choose (m + 1) * (n - m)) * (m + 1) := by ring
      _ = (n.choose (m + 1) * (n + 1)) * (m + 1) := by rw [h2]
      _ = ((m + 1) * n.choose (m + 1)) * (n + 1) := by ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) h_mul

lemma choose_num_eq_den_mul_choose (n m : ℕ) : choose_num n m = choose_den m * n.choose m := by
  induction m with
  | zero =>
    simp [choose_num, choose_den]
  | succ m ih =>
    simp [choose_num, choose_den]
    rw [ih]
    rw [mul_assoc (choose_den m), choose_mul_succ_sub]
    ring

lemma choose_den_pos (m : ℕ) : choose_den m > 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    simp [choose_den]
    omega

lemma choose_fast_eq (n m : ℕ) : choose_fast n m = n.choose m := by
  dsimp [choose_fast]
  split_ifs with h
  · exact (choose_eq_zero_of_lt h).symm
  · have h_le : m ≤ n := by omega
    have h_eq := choose_num_eq_den_mul_choose n m
    have h_pos := choose_den_pos m
    rw [h_eq]
    exact Nat.mul_div_cancel_left (n.choose m) h_pos
