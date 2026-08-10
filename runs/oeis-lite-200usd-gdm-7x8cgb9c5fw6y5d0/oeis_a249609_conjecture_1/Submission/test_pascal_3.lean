import FormalConjectures.Util.ProblemImports

open Nat List

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
