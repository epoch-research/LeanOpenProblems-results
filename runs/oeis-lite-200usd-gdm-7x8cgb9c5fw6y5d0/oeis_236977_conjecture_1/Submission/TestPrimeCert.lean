import FormalConjectures.Util.ProblemImports

open Nat

def no_divisors_loop : Nat → Nat → Nat → Nat → Bool
  | 0, n, low, high =>
    if low = high then n % low != 0 else true
  | fuel + 1, n, low, high =>
    if low > high then true
    else if low = high then n % low != 0
    else
      let mid := (low + high) / 2
      no_divisors_loop fuel n low mid && no_divisors_loop fuel n (mid + 1) high

theorem no_divisors_sound (fuel : Nat) : ∀ n low high, high - low < 2 ^ fuel →
    no_divisors_loop fuel n low high = true →
    ∀ d, low ≤ d → d ≤ high → ¬ d ∣ n := by
  induction fuel with
  | zero =>
    intro n low high h_lt h_all d hd_low hd_high
    have h_d : d = low := by omega
    intro hd_dvd
    rw [h_d] at hd_dvd
    have h_mod : n % low = 0 := Nat.mod_eq_zero_of_dvd hd_dvd
    dsimp [no_divisors_loop] at h_all
    have h_eq : low = high := by omega
    rw [if_pos h_eq] at h_all
    rw [h_mod] at h_all
    contradiction
  | succ f ih =>
    intro n low high h_lt h_all d hd_low hd_high
    dsimp [no_divisors_loop] at h_all
    split_ifs at h_all with h_gt h_eq
    · omega
    · have h_d : d = low := by omega
      intro hd_dvd
      rw [h_d] at hd_dvd
      have h_mod : n % low = 0 := Nat.mod_eq_zero_of_dvd hd_dvd
      rw [h_mod] at h_all
      contradiction
    · rw [Bool.and_eq_true] at h_all
      rcases h_all with ⟨h_left, h_right⟩
      let mid := (low + high) / 2
      have h_mid : mid = (low + high) / 2 := rfl
      have h_div : 2 * mid ≤ low + high ∧ low + high < 2 * mid + 2 := by
        rw [h_mid]
        omega
      by_cases hn : d ≤ mid
      · apply ih n low mid ?_ h_left d hd_low hn
        have : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
        omega
      · apply ih n (mid + 1) high ?_ h_right d ?_ hd_high
        · omega
        · have : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
          omega

theorem prime_of_no_divisors (p : ℕ) (hp : 2 ≤ p)
    (h_no : ∀ d, 2 ≤ d → d ≤ sqrt p → ¬ d ∣ p) : Nat.Prime p := by
  by_contra h_not
  have h_pos : 0 < p := by omega
  have h_sq : minFac p ^ 2 ≤ p := minFac_sq_le_self h_pos h_not
  have h_dvd : minFac p ∣ p := minFac_dvd p
  have h_sq_mul : minFac p * minFac p ≤ p := by
    rw [show minFac p * minFac p = minFac p ^ 2 by ring]
    exact h_sq
  have h_sqrt : minFac p ≤ sqrt p := le_sqrt.mpr h_sq_mul
  have h_p_prime : (minFac p).Prime := minFac_prime (by omega)
  have h_ge : 2 ≤ minFac p := h_p_prime.two_le
  have h_not_dvd := h_no (minFac p) h_ge h_sqrt
  contradiction
