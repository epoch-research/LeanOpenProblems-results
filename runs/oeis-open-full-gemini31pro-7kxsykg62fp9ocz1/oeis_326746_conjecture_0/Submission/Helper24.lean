import Mathlib
import Submission.Helper10

lemma a_100_eq_9 (q d : ℕ) (hd : d < 99) (heq : d % 10 = 9) :
  a_helper (100 * q + d) = 8 % (S q + d / 10 + 1) := by
  unfold a_helper
  have h_S1 : S (100 * q + d) = S q + d / 10 + d % 10 := by
    have : S (100 * q + d) = S (10 * (10 * q + d / 10) + d % 10) := by congr 1; omega
    rw [this]
    rw [S_10 _ (d % 10) (by omega)]
    rw [S_10 q (d / 10) (by omega)]
  have h_S2 : S (100 * q + d + 1) = S q + d / 10 + 1 := by
    have h1 : S (100 * q + d + 1) = S (10 * (10 * q + d / 10 + 1) + 0) := by
      congr 1
      have : d % 10 = 9 := heq
      omega
    rw [h1]
    rw [S_10 _ 0 (by omega)]
    have h2 : 10 * q + d / 10 + 1 = 10 * q + (d / 10 + 1) := by omega
    rw [h2]
    rw [S_10 q (d / 10 + 1) (by omega)]
    omega
  rw [h_S1, h_S2]
  have eq : S q + d / 10 + d % 10 = S q + d / 10 + 9 := by rw [heq]
  rw [eq]
  have : S q + d / 10 + 9 = (S q + d / 10 + 1) + 8 := by omega
  rw [this]
  rw [Nat.add_mod]
  have : (S q + d / 10 + 1) % (S q + d / 10 + 1) = 0 := Nat.mod_self _
  rw [this]
  have : (0 + 8 % (S q + d / 10 + 1)) % (S q + d / 10 + 1) = 8 % (S q + d / 10 + 1) := by
    rw [zero_add]
    exact Nat.mod_mod 8 (S q + d / 10 + 1)
  exact this

lemma a_100_eq (q d : ℕ) (hd : d < 99) (hneq : d % 10 ≠ 9) :
  a_helper (100 * q + d) = S q + d / 10 + d % 10 := by
  unfold a_helper
  have h_S1 : S (100 * q + d) = S q + d / 10 + d % 10 := by
    have : S (100 * q + d) = S (10 * (10 * q + d / 10) + d % 10) := by congr 1; omega
    rw [this]
    rw [S_10 _ (d % 10) (by omega)]
    rw [S_10 q (d / 10) (by omega)]
  have h_S2 : S (100 * q + d + 1) = S q + d / 10 + d % 10 + 1 := by
    have : S (100 * q + d + 1) = S (10 * (10 * q + d / 10) + (d % 10 + 1)) := by congr 1; omega
    rw [this]
    rw [S_10 _ (d % 10 + 1) (by omega)]
    rw [S_10 q (d / 10) (by omega)]
    omega
  rw [h_S1, h_S2]
  apply Nat.mod_eq_of_lt
  omega
