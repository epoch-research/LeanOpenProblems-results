import FormalConjectures.Util.ProblemImports
import Submission.Test2

open Nat

lemma composite_case_contradiction (q : ℕ) (hq : Nat.Prime q) (hq8 : q ≥ 8)
    (ih : ∀ m < q, Nat.Prime m → m ∣ x_seq (m * m - 1))
    (h_ndiv : ¬ (q ∣ x_seq (q - 1)))
    (hp : ¬ Nat.Prime (q + 2)) : False := by
  have h_div_q_plus_2 : q + 2 ∣ x_seq q := by
    have hq2 : q - 1 ≥ 1 := by omega
    have h_fac := factor_lemma (q-1) hq2
    have h_gcd_eq_1 : Nat.gcd (x_seq (q-1)) q = 1 := by
      have h_dvd := Nat.gcd_dvd_right (x_seq (q-1)) q
      have h_cases := Nat.Prime.eq_one_or_self_of_dvd hq _ h_dvd
      rcases h_cases with h1 | h2
      · exact h1
      · have h_gcd_dvd_left := Nat.gcd_dvd_left (x_seq (q-1)) q
        rw [h2] at h_gcd_dvd_left
        contradiction
    have h_fac_val : x_seq q = x_seq (q - 1) * (q + 2) := by
      have h_eq : q - 1 + 1 = q := by omega
      have h_fac' := h_fac
      rw [h_eq] at h_fac'
      rw [h_gcd_eq_1] at h_fac'
      simp at h_fac'
      rw [h_fac']
      ring
    rw [h_fac_val]
    exact dvd_mul_left (q + 2) (x_seq (q - 1))
  have h_dvd_p1 : q + 2 ∣ x_seq (q + 1) := by
    have h_succ : x_seq q ∣ x_seq (q + 1) := x_seq_dvd_x_seq_succ q (by omega)
    exact dvd_trans h_div_q_plus_2 h_succ
  -- Now we follow the logic for the composite case:
  have hM : q + 2 > 0 := by omega
  have hq1 : Nat.minFac (q + 2) * Nat.minFac (q + 2) ≤ q + 2 :=
    minfac_sq_le_of_composite (q + 2) hM hp
  generalize hq1_eq : Nat.minFac (q + 2) = q'
  rw [hq1_eq] at hq1
  have hq'_prime : Nat.Prime q' := by
    rw [← hq1_eq]
    apply Nat.minFac_prime
    omega
  -- We want to prove q' < q
  have hq'_lt : q' < q := by
    by_contra h_ge
    have h_ge' : q' ≥ q := by omega
    have h_sq_ge : q' * q' ≥ q * q := Nat.mul_le_mul h_ge' h_ge'
    have h_q_sq : q * q > q + 2 := by
      have : q * q ≥ 8 * q := Nat.mul_le_mul_right q hq8
      omega
    omega
  have h_dvd_q'_sq := ih q' hq'_lt hq'_prime
  -- Since q' is the smallest prime factor of q+2, and q+2 is odd (since q is prime and ≥ 11, so q is odd)
  have h_odd_q : q % 2 = 1 := Nat.Prime.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have h_odd_M : (q + 2) % 2 = 1 := by
    rw [Nat.add_mod]
    rw [h_odd_q]
    rfl
  have hq'_odd : q' % 2 = 1 := by
    have h_dvd : q' ∣ q + 2 := by
      rw [← hq1_eq]
      exact Nat.minFac_dvd (q + 2)
    -- since q' divides an odd number, q' must be odd
    by_contra h_even
    have : q' = 2 := by
      -- since q' is prime and not odd, it must be 2
      have : q' % 2 = 0 := Nat.mod_two_of_not_odd h_even
      rcases Nat.Prime.eq_two_or_odd hq'_prime with rfl | h_odd
      · rfl
      · contradiction
    rw [this] at h_dvd
    have : 2 ∣ (q + 2) := h_dvd
    have : (q + 2) % 2 = 0 := Nat.mod_two_of_dvd this
    omega
  have hq'_ge_3 : q' ≥ 3 := by
    have : q' ≥ 2 := Nat.Prime.two_le hq'_prime
    have : q' ≠ 2 := by
      intro hc
      rw [hc] at hq'_odd
      contradiction
    omega
  -- We want to show q' * q' ≤ q
  have hq'_sq_le_q : q' * q' ≤ q := by
    -- We have q' * q' ≤ q + 2
    -- Since q' * q' is odd, and q + 2 is odd.
    -- Can q' * q' = q + 1? No, q + 1 is even.
    -- Can q' * q' = q + 2?
    -- If q' * q' = q + 2, then we need to handle this.
    sorry
  sorry





