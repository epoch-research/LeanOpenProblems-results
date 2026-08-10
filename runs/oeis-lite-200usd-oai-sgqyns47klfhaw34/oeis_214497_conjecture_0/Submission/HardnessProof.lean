import FormalConjectures.Util.ProblemImports

open Nat

/-- Twin prime centers. -/
def Center (m : ℕ) : Prop := Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)

lemma center_pos_of_center {m : ℕ} (h : Center m) : 0 < m := by
  by_contra hm
  push_neg at hm
  have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
  have : ¬ Nat.Prime (m - 1) := by simpa [hm0] using Nat.not_prime_zero
  exact this h.1

lemma center_ne_zero_of_center {m : ℕ} (h : Center m) : m ≠ 0 := by
  exact Nat.ne_of_gt (center_pos_of_center h)

lemma two_pow_dvd_center_of_witness {n k : ℕ}
    (h : Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧
         Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) :
    2 ^ n ∣ (3 ^ n - k) * (2 ^ n) := by
  exact dvd_mul_left _ _

lemma center_from_witness {n k : ℕ}
    (h : Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧
         Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) :
    Center ((3 ^ n - k) * (2 ^ n)) := h

-- If a nonzero number is divisible by arbitrarily high powers of 2, contradiction.
#check Nat.dvd_antisymm
#check Nat.pow_lt_pow_right
#check Nat.lt_of_dvd_of_lt
#check Nat.dvd_trans
#check Nat.exists_pow_gt
#check pow_unbounded_of_one_lt
#check exists_lt_pow
#check Nat.exists_pow_gt

