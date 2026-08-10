import FormalConjectures.Util.ProblemImports

open Nat

lemma sq_identity (y z : ℕ) (h : y ≥ 1 ∨ z ≥ 1) :
    (2 * y ^ 2 + 4 * z ^ 2 - 1) ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = (2 * y ^ 2 + 4 * z ^ 2 + 1) ^ 2 := by
  have h_le : 1 ≤ 2 * y ^ 2 + 4 * z ^ 2 := by
    rcases h with hy | hz
    · have : 2 * y ^ 2 ≥ 2 := by nlinarith
      omega
    · have : 4 * z ^ 2 ≥ 4 := by nlinarith
      omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_le)
  have hk_sub : 2 * y ^ 2 + 4 * z ^ 2 - 1 = k := by omega
  rw [hk_sub]
  have h_assoc : k ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = k ^ 2 + (8 * y ^ 2 + 16 * z ^ 2) := by omega
  rw [h_assoc]
  have h_eq : 8 * y ^ 2 + 16 * z ^ 2 = 4 * k + 4 := by omega
  rw [h_eq]
  have h_eq2 : 2 * y ^ 2 + 4 * z ^ 2 + 1 = k + 2 := by omega
  rw [h_eq2]
  ring
