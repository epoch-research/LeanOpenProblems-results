import FormalConjectures.Util.ProblemImports

open Finset

lemma sum_range_sq (n : ℕ) : 6 * ∑ i ∈ range n, i ^ 2 = (n - 1) * n * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    rcases n with _ | n
    · simp
    · -- n is succ n. So n ≥ 1. Let's rewrite subtraction away.
      have h1 : n.succ - 1 = n := by omega
      have h2 : 2 * n.succ - 1 = 2 * n + 1 := by omega
      rw [h1, h2]
      have h_int : (((n * n.succ * (2 * n + 1) + 6 * n.succ ^ 2 : ℕ) : ℤ) = ((n.succ * (n.succ + 1) * (2 * n.succ + 1) : ℕ) : ℤ)) := by
        push_cast
        ring
      exact_mod_cast h_int

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma A048153_eq_sum_sub (n : ℕ) : 
    ((A048153 n : ℕ) : ℤ) = ((∑ k ∈ range n, k^2 : ℕ) : ℤ) - n * ((∑ k ∈ range n, (k^2 / n) : ℕ) : ℤ) := by
  have h_sum : ((A048153 n : ℕ) : ℤ) = ∑ k ∈ range n, (((k^2 % n : ℕ) : ℤ)) := by
    simp [A048153]
  rw [h_sum]
  have h_term (k : ℕ) : ((k^2 % n : ℕ) : ℤ) = ((k^2 : ℕ) : ℤ) - (n : ℤ) * ((k^2 / n : ℕ) : ℤ) := by
    have h_div_mod : k^2 = n * (k^2 / n) + k^2 % n := (Nat.div_add_mod (k^2) n).symm
    have h_div_mod_cast : ((k^2 : ℕ) : ℤ) = (n : ℤ) * ((k^2 / n : ℕ) : ℤ) + ((k^2 % n : ℕ) : ℤ) := by
      exact_mod_cast h_div_mod
    omega
  have h_sub : (fun k => ((k^2 % n : ℕ) : ℤ)) = (fun k => ((k^2 : ℕ) : ℤ) - (n : ℤ) * ((k^2 / n : ℕ) : ℤ)) := by
    funext k
    exact h_term k
  rw [h_sub]
  rw [sum_sub_distrib]
  rw [← Finset.mul_sum]
  push_cast
  rfl

lemma S_lower_bound (n : ℕ) (hn : 5 ≤ n) : 
    ((n - 1) * (n - 2) : ℤ) ≤ 3 * ((∑ k ∈ range n, (k^2 / n) : ℕ) : ℤ) := by
  sorry

lemma A048153_le_n_mul_sub (n : ℕ) (hn : 5 ≤ n) : A048153 n ≤ n * (n - 1) / 2 := by
  have h_id := A048153_eq_sum_sub n
  have h_sq : 6 * ∑ k ∈ range n, ((k : ℤ)^2) = (((n - 1) * n * (2 * n - 1) : ℕ) : ℤ) := by
    have h_sq_nat := sum_range_sq n
    exact_mod_cast h_sq_nat
  have h_low := S_lower_bound n hn
  have h_mul_int : 2 * ((A048153 n : ℕ) : ℤ) ≤ (n : ℤ) * ((n : ℤ) - 1) := by
    have h_mul6 : 6 * ((A048153 n : ℕ) : ℤ) ≤ 3 * (n : ℤ) * ((n : ℤ) - 1) := by
      have h1 : 6 * ((A048153 n : ℕ) : ℤ) = 6 * (((∑ k ∈ range n, k^2 : ℕ) : ℤ)) - 2 * (n : ℤ) * (3 * ((∑ k ∈ range n, (k^2 / n) : ℕ) : ℤ)) := by
        rw [h_id]
        ring
      rw [h1]
      have h_sq_int : 6 * (((∑ k ∈ range n, k^2 : ℕ) : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) * (2 * (n : ℤ) - 1) := by
        have h_cast_sq : (((∑ k ∈ range n, k^2 : ℕ) : ℤ)) = ∑ k ∈ range n, ((k : ℤ)^2) := by push_cast; rfl
        rw [h_cast_sq, h_sq]
        have h1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (by omega)
        have h2 : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := Nat.cast_sub (by omega)
        push_cast
        rw [h1, h2]
        ring
      rw [h_sq_int]
      have : 0 ≤ 2 * (n : ℤ) := by omega
      nlinarith [h_low]
    have h_mul6_rw : 3 * (2 * ((A048153 n : ℕ) : ℤ)) ≤ 3 * ((n : ℤ) * ((n : ℤ) - 1)) := by
      have h_lhs : 3 * (2 * ((A048153 n : ℕ) : ℤ)) = 6 * ((A048153 n : ℕ) : ℤ) := by ring
      rw [h_lhs]
      have h_rhs : 3 * ((n : ℤ) * ((n : ℤ) - 1)) = 3 * (n : ℤ) * ((n : ℤ) - 1) := by ring
      rw [h_rhs]
      exact h_mul6
    omega
  have h_mul_nat : 2 * A048153 n ≤ n * (n - 1) := by
    have h_goal_cast : ((2 * A048153 n : ℕ) : ℤ) ≤ ((n * (n - 1) : ℕ) : ℤ) := by
      push_cast
      have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (by omega)
      rw [this]
      exact h_mul_int
    exact_mod_cast h_goal_cast
  omega







