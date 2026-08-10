import FormalConjectures.Util.ProblemImports
open Nat Int

lemma factorial_gt_quadratic {n : ℕ} (hn : 4 ≤ n) : 2 * n.factorial > n * (n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_mul : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_mul]
    have h1 : 2 * m.factorial > m * (m + 1) := ih
    have h2 : (m + 1) * (2 * m.factorial) > (m + 1) * (m * (m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left h1 (by omega)
    have h3 : m * (m + 1) ≥ m + 2 := by
      calc m * (m + 1) ≥ 4 * (m + 1) := Nat.mul_le_mul_right (m + 1) hm
        _ = 4 * m + 4 := by ring
        _ ≥ m + 2 := by omega
    have h4 : (m + 1) * (m * (m + 1)) ≥ (m + 1) * (m + 2) := Nat.mul_le_mul_left (m + 1) h3
    exact lt_of_le_of_lt h4 h2

lemma factorial_gt_two_n_mul {n : ℕ} (hn : 5 ≤ n) : 2 * n.factorial ≥ 2 * n * (2 * n - 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_eq]
    have ih' : 2 * m.factorial ≥ 2 * m * (2 * m - 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) ≥ (m + 1) * (2 * m * (2 * m - 1)) := Nat.mul_le_mul_left (m + 1) ih'
    have h2 : (m + 1) * (2 * m * (2 * m - 1)) ≥ 2 * (m + 1) * (2 * (m + 1) - 1) := by
      have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [this]
      have h3 : m * (2 * m - 1) ≥ 2 * m + 1 := by
        have h_sub : m * (2 * m - 1) = 2 * m * m - m := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          congr 1
          ring
        rw [h_sub]
        have h_quad : 2 * m * m ≥ 10 * m := by
          calc 2 * m * m = (2 * m) * m := by ring
            _ ≥ (2 * 5) * m := Nat.mul_le_mul_right m (by omega)
            _ = 10 * m := by ring
        omega
      have h4 : 2 * (m + 1) * (m * (2 * m - 1)) ≥ 2 * (m + 1) * (2 * m + 1) := Nat.mul_le_mul_left (2 * (m + 1)) h3
      have h_comm : (m + 1) * (2 * m * (2 * m - 1)) = 2 * (m + 1) * (m * (2 * m - 1)) := by ring
      rw [h_comm]
      exact h4
    exact le_trans h2 h1

lemma k_ge_two_n {n k : ℕ} (h_eq : 2 * n.factorial = k * (k + 1)) (hn : 5 ≤ n) : k + 1 ≥ 2 * n := by
  by_contra hc
  have hk : k + 1 < 2 * n := by omega
  have hk2 : k < 2 * n - 1 := by omega
  have h_lt : k * (k + 1) < 2 * n * (2 * n - 1) := by
    have h1 : k * (k + 1) < (2 * n - 1) * (k + 1) := by
      exact mul_lt_mul_of_pos_right hk2 (by omega)
    have h2 : (2 * n - 1) * (k + 1) < (2 * n - 1) * (2 * n) := by
      exact mul_lt_mul_of_pos_left hk (by omega)
    have h3 : k * (k + 1) < (2 * n - 1) * (2 * n) := lt_trans h1 h2
    rwa [Nat.mul_comm (2 * n - 1) (2 * n)] at h3
  have h_ge : 2 * n.factorial ≥ 2 * n * (2 * n - 1) := factorial_gt_two_n_mul hn
  omega
