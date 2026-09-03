import FormalConjecturesUtil

/-!
An auxiliary obstruction, not a disproof of Erdős 773.
Even arbitrarily large gaps between the nonzero binary digits do not by
themselves guarantee Sidon squares. The roots below have at most two
nonzero binary digits.
-/

namespace Erdos773

lemma sparse_digit_collision_identity (q : ℕ) :
    (2 * q) ^ 2 + (2 * q ^ 4 + 1) ^ 2 =
      (2 * q ^ 2 + 1) ^ 2 + (2 * q ^ 4) ^ 2 := by
  ring

lemma sparse_digit_collision_not_sidon (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsSidon ({(2 * q) ^ 2, (2 * q ^ 4 + 1) ^ 2,
      (2 * q ^ 2 + 1) ^ 2, (2 * q ^ 4) ^ 2} : Set ℕ) := by
  have hq2 : q < q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hac : 2 * q < 2 * q ^ 2 + 1 := by omega
  have had : 2 * q < 2 * q ^ 4 := by omega
  have hac2 := Nat.pow_lt_pow_left hac (by omega : (2 : ℕ) ≠ 0)
  have had2 := Nat.pow_lt_pow_left had (by omega : (2 : ℕ) ≠ 0)
  intro h
  have he := h _ (by simp) _ (by simp) _ (by simp) _ (by simp)
    (sparse_digit_collision_identity q)
  rcases he with he | he <;> omega

lemma arbitrarily_separated_binary_collision (k : ℕ) :
    (2 ^ (k + 2)) ^ 2 + (2 ^ (4 * k + 5) + 1) ^ 2 =
      (2 ^ (2 * k + 3) + 1) ^ 2 + (2 ^ (4 * k + 5)) ^ 2 ∧
    ¬ IsSidon ({(2 ^ (k + 2)) ^ 2, (2 ^ (4 * k + 5) + 1) ^ 2,
      (2 ^ (2 * k + 3) + 1) ^ 2, (2 ^ (4 * k + 5)) ^ 2} : Set ℕ) := by
  have hq : 2 ≤ (2 : ℕ) ^ (k + 1) := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
      (show 1 ≤ k + 1 by omega))
  have h1 : 2 * (2 : ℕ) ^ (k + 1) = 2 ^ (k + 2) := by
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ]
    omega
  have h2 : 2 * ((2 : ℕ) ^ (k + 1)) ^ 2 = 2 ^ (2 * k + 3) := by
    rw [← pow_mul, show 2 * k + 3 = (k + 1) * 2 + 1 by omega, pow_succ]
    omega
  have h4 : 2 * ((2 : ℕ) ^ (k + 1)) ^ 4 = 2 ^ (4 * k + 5) := by
    rw [← pow_mul, show 4 * k + 5 = (k + 1) * 4 + 1 by omega, pow_succ]
    omega
  constructor
  · simpa only [h1, h2, h4] using sparse_digit_collision_identity (2 ^ (k + 1))
  · simpa only [h1, h2, h4] using sparse_digit_collision_not_sidon (2 ^ (k + 1)) hq

#print axioms arbitrarily_separated_binary_collision

end Erdos773
