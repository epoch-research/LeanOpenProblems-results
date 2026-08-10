import FormalConjectures.Util.ProblemImports
open Nat

def D : ℕ := 4031017571163409250897522631853874805931471009

lemma factorial_gt_huge {n : ℕ} (hn : 67 ≤ n) : 2 * n.factorial > (D - 1) * n * ((D - 1) * n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_eq]
    have ih' : 2 * m.factorial > (D - 1) * m * ((D - 1) * m + 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) > (m + 1) * ((D - 1) * m * ((D - 1) * m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left ih' (by omega)
    have h2 : (m + 1) * ((D - 1) * m * ((D - 1) * m + 1)) ≥ (D - 1) * (m + 1) * ((D - 1) * (m + 1) + 1) := by
      have h_comm1 : (m + 1) * ((D - 1) * m * ((D - 1) * m + 1)) = (D - 1) * (m + 1) * (m * ((D - 1) * m + 1)) := by ring
      rw [h_comm1]
      have h3 : m * ((D - 1) * m + 1) ≥ (D - 1) * (m + 1) + 1 := by
        have h_mul1 : m * ((D - 1) * m + 1) = (D - 1) * m * m + m := by ring
        have h_mul2 : (D - 1) * (m + 1) + 1 = (D - 1) * m + D := by unfold D; omega
        rw [h_mul1, h_mul2]
        have h_quad : (D - 1) * m * m ≥ (D - 1) * m + D := by
          calc (D - 1) * m * m = ((D - 1) * m) * m := by ring
            _ ≥ ((D - 1) * m) * 67 := Nat.mul_le_mul_left _ hm
            _ = (D - 1) * m * 1 + (D - 1) * m * 66 := by ring
            _ ≥ (D - 1) * m * 1 + (D - 1) * 67 * 66 := by
              have : (D - 1) * m * 66 ≥ (D - 1) * 67 * 66 := by
                have : (D - 1) * m ≥ (D - 1) * 67 := Nat.mul_le_mul_left _ hm
                omega
              omega
            _ ≥ (D - 1) * m + D := by
              have : (D - 1) * 67 * 66 ≥ D := by
                unfold D; omega
              omega
        unfold D at h_quad ⊢
        omega
      exact Nat.mul_le_mul_left _ h3
    exact lt_of_le_of_lt h2 h1
