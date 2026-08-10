import FormalConjectures.Util.ProblemImports
open Finset

lemma sum_if_term_odd (H : ℕ) (hH : 4 ≤ H) :
    ∑ k ∈ range (2 * H + 1), (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) = 8 * H ^ 2 - 6 * H + 3 := by
  have h_eq : 2 * H + 1 = 3 + (2 * H - 2) := by omega
  rw [h_eq]
  rw [sum_range_add]
  have h_first : ∑ k ∈ range 3, (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) = 5 := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
    simp
  have h_second : ∑ k ∈ range (2 * H - 2), (if 3 + k = 0 then (0:ℕ) else if 3 + k = 1 then 1 else if 3 + k = 2 then 4 else 4 * H + 1) = ∑ k ∈ range (2 * H - 2), (4 * H + 1) := by
    apply sum_congr rfl
    intro k hk
    have : 3 + k ≠ 0 := by omega
    have : 3 + k ≠ 1 := by omega
    have : 3 + k ≠ 2 := by omega
    split_ifs <;> omega
  rw [h_first, h_second]
  rw [sum_const, card_range, nsmul_eq_mul]
  have h_sub3 : 6 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_sub4 : 2 ≤ 2 * H := by omega
  have h_cast1 : ((2 * H - 2 : ℕ) : ℤ) = 2 * (H : ℤ) - 2 := by
    rw [Nat.cast_sub h_sub4]
    push_cast
    rfl
  have h_cast3 : ((8 * H ^ 2 - 6 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 6 * (H : ℤ) := by
    rw [Nat.cast_sub h_sub3]
    push_cast
    rfl
  zify
  rw [h_cast1, h_cast3]
  ring
