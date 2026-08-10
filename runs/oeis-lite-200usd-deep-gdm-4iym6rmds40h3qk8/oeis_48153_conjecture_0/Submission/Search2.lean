import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma Nat.sq_sub_add_mul_self (n k : ℕ) (h : k ≤ n) :
    (n - k) ^ 2 + 2 * n * k = n ^ 2 + k ^ 2 := by
  have h_int : ((n - k : ℕ) : ℤ) ^ 2 + 2 * (n : ℤ) * (k : ℤ) = (n : ℤ) ^ 2 + (k : ℤ) ^ 2 := by
    rw [Nat.cast_sub h]
    ring
  exact_mod_cast h_int

lemma sq_sub_mod (n k : ℕ) (h : k ≤ n) : (n - k) ^ 2 % n = k ^ 2 % n := by
  have h1 : (n - k) ^ 2 + 2 * n * k = n ^ 2 + k ^ 2 := Nat.sq_sub_add_mul_self n k h
  have h2 : ((n - k) ^ 2 + 2 * n * k) % n = (n ^ 2 + k ^ 2) % n := by rw [h1]
  have hLHS : ((n - k) ^ 2 + 2 * n * k) % n = (n - k) ^ 2 % n := by
    have : 2 * n * k = n * (2 * k) := by ring
    rw [this, Nat.add_mul_mod_self_left]
  have hRHS : (n ^ 2 + k ^ 2) % n = k ^ 2 % n := by
    have : n ^ 2 + k ^ 2 = k ^ 2 + n * n := by ring
    rw [this, Nat.add_mul_mod_self_left]
  rw [hLHS, hRHS] at h2
  exact h2

lemma sq_mod_le_mul_sub (n k : ℕ) (h : k < n) : k ^ 2 % n ≤ k * (n - k) := by
  by_cases h_le : k ≤ n - k
  · have h1 : k ^ 2 % n ≤ k ^ 2 := Nat.mod_le (k ^ 2) n
    have h2 : k ^ 2 ≤ k * (n - k) := by
      rw [sq]
      exact Nat.mul_le_mul_left k h_le
    exact Nat.le_trans h1 h2
  · push_neg at h_le
    have h1 : k ^ 2 % n = (n - k) ^ 2 % n := (sq_sub_mod n k (by omega)).symm
    have h2 : (n - k) ^ 2 % n ≤ (n - k) ^ 2 := Nat.mod_le ((n - k) ^ 2) n
    have h3 : (n - k) ^ 2 ≤ k * (n - k) := by
      rw [sq]
      exact Nat.mul_le_mul_right (n - k) (by omega)
    rw [h1]
    exact Nat.le_trans h2 h3

lemma sq_mod_le_mul_sub_one_div (n k : ℕ) (hn : 5 ≤ n) (h : k < n) : k ^ 2 % n ≤ k * (n - 1) / 2 := by
  by_cases h_le : 2 * k ≤ n - 1
  · have h1 : k ^ 2 % n ≤ k ^ 2 := Nat.mod_le _ _
    have h2 : 2 * (k ^ 2 % n) ≤ k * (n - 1) := by
      calc 2 * (k ^ 2 % n) ≤ 2 * k ^ 2 := by omega
      _ = k * (2 * k) := by ring
      _ ≤ k * (n - 1) := Nat.mul_le_mul_left k h_le
    omega
  · push_neg at h_le
    have h_sub_le : 2 * (n - k) ≤ n := by omega
    by_cases h_sub_le_sub_one : 2 * (n - k) ≤ n - 1
    · have h1 : k ^ 2 % n = (n - k) ^ 2 % n := (sq_sub_mod n k (by omega)).symm
      have h_mod_le : (n - k) ^ 2 % n ≤ (n - k) ^ 2 := Nat.mod_le _ _
      have h2 : 2 * ((n - k) ^ 2 % n) ≤ k * (n - 1) := by
        calc 2 * ((n - k) ^ 2 % n) ≤ 2 * (n - k) ^ 2 := by omega
        _ = (n - k) * (2 * (n - k)) := by ring
        _ ≤ (n - k) * (n - 1) := Nat.mul_le_mul_left (n - k) h_sub_le_sub_one
        _ ≤ k * (n - 1) := Nat.mul_le_mul_right (n - 1) (by omega)
      rw [h1]
      omega
    · push_neg at h_sub_le_sub_one
      have h_eq : 2 * (n - k) = n := by omega
      have h_eq2 : n - k = k := by omega
      have h_m : n - k = n / 2 := by omega
      have hn6 : 6 ≤ n := by omega
      have hm3 : 3 ≤ n / 2 := by omega
      have hn_sub_1 : 5 ≤ n - 1 := by omega
      have h_lt : k ^ 2 % n < n := Nat.mod_lt _ (by omega)
      have h_ineq : 2 * (k ^ 2 % n) ≤ k * (n - 1) := by
        have h_lt2 : 2 * (k ^ 2 % n) < 2 * n := by omega
        have h_eq3 : 2 * n = k * 4 := by omega
        have h_le3 : k * 4 ≤ k * (n - 1) := by
          have : 4 ≤ n - 1 := by omega
          exact Nat.mul_le_mul_left k this
        omega
      omega

lemma sq_mod_le_sub_mul_div (n k : ℕ) (hn : 5 ≤ n) (h : k < n) : k ^ 2 % n ≤ (n - k) * (n - 1) / 2 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have h_sub : n - k < n := by omega
    have h1 : k ^ 2 % n = (n - k) ^ 2 % n := (sq_sub_mod n k (by omega)).symm
    rw [h1]
    exact sq_mod_le_mul_sub_one_div n (n - k) hn h_sub

lemma sq_mod_le_add_mul_sub (n k : ℕ) (h : k < n) (hn : 5 ≤ n) : 2 * (k ^ 2 % n) ≤ n - 1 + k * (n - k) := by
  by_cases h_le : k * (n - k) ≤ n - 1
  · have h1 : k ^ 2 % n ≤ k * (n - k) := sq_mod_le_mul_sub n k h
    omega
  · push_neg at h_le
    have h2 : k ^ 2 % n ≤ n - 1 := by
      have : k ^ 2 % n < n := Nat.mod_lt _ (by omega)
      omega
    omega

theorem search_proof (n : ℕ) (h : 5 ≤ n) : A048153 n ≤ n * (n - 1) / 2 := by
  aesop (add unsafe [sq_mod_le_mul_sub_one_div, sq_mod_le_sub_mul_div, sq_mod_le_add_mul_sub])

