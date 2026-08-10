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

theorem search_proof (n : ℕ) (hn : 5 ≤ n) : A048153 n ≤ ∑ k ∈ range n, k * (n - 1) / 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have h_lt : k < n := Finset.mem_range.mp hk
  exact sq_mod_le_mul_sub_one_div n k hn h_lt


theorem sum_split (n : ℕ) : A048153 n = ∑ k ∈ range (n / 2), k ^ 2 % n + ∑ k ∈ Ico (n / 2) n, k ^ 2 % n := by
  have : n / 2 ≤ n := Nat.div_le_self n 2
  exact (Finset.sum_range_add_sum_Ico (fun k => k ^ 2 % n) this).symm


lemma sq_mod_le_sub_mul_div (n k : ℕ) (hn : 5 ≤ n) (h : k < n) : k ^ 2 % n ≤ (n - k) * (n - 1) / 2 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have h_sub : n - k < n := by omega
    have h1 : k ^ 2 % n = (n - k) ^ 2 % n := (sq_sub_mod n k (by omega)).symm
    rw [h1]
    exact sq_mod_le_mul_sub_one_div n (n - k) hn h_sub

theorem part1_bound (n : ℕ) (hn : 5 ≤ n) : ∑ k ∈ range (n / 2), k ^ 2 % n ≤ ∑ k ∈ range (n / 2), k * (n - 1) / 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have h_lt : k < n / 2 := Finset.mem_range.mp hk
  have h_lt2 : k < n := by
    have : n / 2 ≤ n := Nat.div_le_self n 2
    omega
  exact sq_mod_le_mul_sub_one_div n k hn h_lt2

theorem part2_bound (n : ℕ) (hn : 5 ≤ n) : ∑ k ∈ Ico (n / 2) n, k ^ 2 % n ≤ ∑ k ∈ Ico (n / 2) n, (n - k) * (n - 1) / 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have h_lt : k < n := (Finset.mem_Ico.mp hk).2
  exact sq_mod_le_sub_mul_div n k hn h_lt


theorem nat_div_add_le (a b : ℕ) : a / 2 + b / 2 ≤ (a + b) / 2 := by
  omega


theorem div_sum_le (n : ℕ) (hn : 5 ≤ n) (k : ℕ) (hk : k < n) :
    k * (n - 1) / 2 + (n - k) * (n - 1) / 2 ≤ n * (n - 1) / 2 := by
  have h1 : k * (n - 1) / 2 + (n - k) * (n - 1) / 2 ≤ (k * (n - 1) + (n - k) * (n - 1)) / 2 := nat_div_add_le _ _
  have h2 : k * (n - 1) + (n - k) * (n - 1) = n * (n - 1) := by
    rw [← Nat.add_mul]
    have : k + (n - k) = n := Nat.add_sub_of_le (Nat.le_of_lt hk)
    rw [this]
  rw [h2] at h1
  exact h1

