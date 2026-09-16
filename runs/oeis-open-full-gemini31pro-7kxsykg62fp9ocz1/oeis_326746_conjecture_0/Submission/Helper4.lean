import Mathlib

lemma poly_sum_bound (k C : ℕ) : ∑ d ∈ Finset.range (C + 1), (k + 1) ^ (C - d) ≤ (k + 2) ^ C := by
  induction C with
  | zero => simp
  | succ C ih =>
    have : ∑ d ∈ Finset.range (C + 1 + 1), (k + 1) ^ (C + 1 - d) =
           (k + 1) ^ (C + 1) + ∑ d ∈ Finset.range (C + 1), (k + 1) ^ (C - d) := by
      rw [Finset.sum_range_succ']
      have h0 : (k + 1) ^ (C + 1 - 0) = (k + 1) ^ (C + 1) := by rfl
      rw [h0]
      have h1 : ∑ i ∈ Finset.range (C + 1), (k + 1) ^ (C + 1 - (i + 1)) = ∑ d ∈ Finset.range (C + 1), (k + 1) ^ (C - d) := by
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        omega
      rw [h1]
      apply add_comm
    rw [this]
    have h1 : (k + 1) ^ (C + 1) + ∑ d ∈ Finset.range (C + 1), (k + 1) ^ (C - d) ≤
              (k + 1) ^ (C + 1) + (k + 2) ^ C := Nat.add_le_add_left ih _
    have h2 : (k + 1) ^ (C + 1) + (k + 2) ^ C ≤ (k + 2) ^ (C + 1) := by
      calc (k + 1) ^ (C + 1) + (k + 2) ^ C
        _ = (k + 1) ^ C * (k + 1) + (k + 2) ^ C := by ring
        _ ≤ (k + 2) ^ C * (k + 1) + (k + 2) ^ C := by
            apply Nat.add_le_add_right
            apply Nat.mul_le_mul_right
            exact Nat.pow_le_pow_left (by omega) _
        _ = (k + 2) ^ C * (k + 2) := by ring
        _ = (k + 2) ^ (C + 1) := by ring
    exact h1.trans h2
