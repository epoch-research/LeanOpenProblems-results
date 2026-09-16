import Submission.Lemmas8
import Mathlib

lemma odd_jump (n : ℕ) (hn : 2 ≤ n) : d n % 2 = 1 ∨ d n = 2 := by
  have hd : d n =
    if n % 2 = 0 then
      Nat.gcd n (C (n - 1) - 1)
    else
      Nat.gcd (n - 2) (C (n - 1) + 1) := d_val2 n hn
  rw [hd]
  split_ifs with h_even
  · have h_C_even : C (n - 1) % 2 = 0 ∨ n - 1 = 1 := by
      have h2 : n - 1 = 1 ∨ 2 ≤ n - 1 := by omega
      rcases h2 with h2 | h2
      · right; exact h2
      · left; exact C_even (n - 1) h2
    rcases h_C_even with h_C_even | h2
    · left
      have h_C_odd : (C (n - 1) - 1) % 2 = 1 := by
        have : 1 ≤ C (n - 1) := C_ge_one (n - 1) (by omega)
        omega
      exact gcd_odd_is_odd2 _ _ h_C_odd
    · rw [h2]
      have : C 1 = 1 := rfl
      rw [this]
      right
      have : n = 2 := by omega
      subst this
      rfl
  · have h_C_even : C (n - 1) % 2 = 0 ∨ n - 1 = 1 := by
      have h2 : n - 1 = 1 ∨ 2 ≤ n - 1 := by omega
      rcases h2 with h2 | h2
      · right; exact h2
      · left; exact C_even (n - 1) h2
    rcases h_C_even with h_C_even | h2
    · left
      have h_C_odd : (C (n - 1) + 1) % 2 = 1 := by omega
      exact gcd_odd_is_odd2 _ _ h_C_odd
    · have : n = 2 := by omega
      omega

lemma diff_record_odd (R : ℕ) (h_rec : is_difference_record R) : R % 2 = 1 ∨ R = 2 := by
  rcases h_rec with ⟨n, hn, hd, _⟩
  have : d n % 2 = 1 ∨ d n = 2 := odd_jump n hn
  omega

