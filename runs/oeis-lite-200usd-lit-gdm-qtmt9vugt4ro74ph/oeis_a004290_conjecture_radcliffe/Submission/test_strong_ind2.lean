import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 1000000

theorem dvd_1000_of_dvd_10000_of_lt_10 (d : ℕ) (hd : d ∣ 10000) (h_lt : d < 10) : d ∣ 1000 := by
  interval_cases d
  · contradiction
  · decide
  · decide
  · revert hd; decide
  · decide
  · decide
  · revert hd; decide
  · revert hd; decide
  · decide
  · revert hd; decide

theorem gcd_u_10_eq_one (n : ℕ) (hn : n > 0) :
    let d := Nat.gcd n 10000
    let u := n / d
    d < 10 → Nat.gcd u 10 = 1 := by
  intro d u h_lt
  have hd_eq : d = Nat.gcd n 10000 := rfl
  have hu_eq : u = n / d := rfl
  have hd_dvd_n : d ∣ n := Nat.gcd_dvd_left n 10000
  have hd_dvd_10k : d ∣ 10000 := Nat.gcd_dvd_right n 10000
  have hd_pos : d > 0 := by
    apply Nat.gcd_pos_of_pos_right n (by norm_num)
  have hn_eq_ud : n = u * d := (Nat.div_mul_cancel hd_dvd_n).symm
  have h_gcd_dvd_u : Nat.gcd u 10 ∣ u := Nat.gcd_dvd_left u 10
  have h_gcd_dvd_10 : Nat.gcd u 10 ∣ 10 := Nat.gcd_dvd_right u 10
  have h_gcd_pos : Nat.gcd u 10 > 0 := by
    apply Nat.gcd_pos_of_pos_right u (by norm_num)
  by_contra h_not_one
  have h_gt_one : Nat.gcd u 10 > 1 := by omega
  have h_div_2_or_5 : 2 ∣ Nat.gcd u 10 ∨ 5 ∣ Nat.gcd u 10 := by
    have h_dvd := h_gcd_dvd_10
    have h_gcd_le : Nat.gcd u 10 ≤ 10 := Nat.le_of_dvd (by norm_num) h_gcd_dvd_10
    interval_cases Nat.gcd u 10
    · left; decide
    · revert h_dvd; decide
    · revert h_dvd; decide
    · right; decide
    · revert h_dvd; decide
    · revert h_dvd; decide
    · revert h_dvd; decide
    · revert h_dvd; decide
    · left; decide
  rcases h_div_2_or_5 with h2 | h5
  · have h2_u : 2 ∣ u := dvd_trans h2 h_gcd_dvd_u
    rcases h2_u with ⟨q, hq⟩
    have h2d_n : 2 * d ∣ n := by
      rw [hn_eq_ud, hq]
      use q
      ring
    have h2d_10k : 2 * d ∣ 10000 := by
      interval_cases d
      · decide
      · decide
      · revert hd_dvd_10k; decide
      · decide
      · decide
      · revert hd_dvd_10k; decide
      · revert hd_dvd_10k; decide
      · decide
      · revert hd_dvd_10k; decide
    have h2d_gcd : 2 * d ∣ d := by
      have h2d_gcd_prep := Nat.dvd_gcd h2d_n h2d_10k
      rw [← hd_eq] at h2d_gcd_prep
      exact h2d_gcd_prep
    have h_le_d : 2 * d ≤ d := Nat.le_of_dvd hd_pos h2d_gcd
    omega
  · have h5_u : 5 ∣ u := dvd_trans h5 h_gcd_dvd_u
    rcases h5_u with ⟨q, hq⟩
    have h5d_n : 5 * d ∣ n := by
      rw [hn_eq_ud, hq]
      use q
      ring
    have h5d_10k : 5 * d ∣ 10000 := by
      interval_cases d
      · decide
      · decide
      · revert hd_dvd_10k; decide
      · decide
      · decide
      · revert hd_dvd_10k; decide
      · revert hd_dvd_10k; decide
      · decide
      · revert hd_dvd_10k; decide
    have h5d_gcd : 5 * d ∣ d := by
      have h5d_gcd_prep := Nat.dvd_gcd h5d_n h5d_10k
      rw [← hd_eq] at h5d_gcd_prep
      exact h5d_gcd_prep
    have h_le_d : 5 * d ≤ d := Nat.le_of_dvd hd_pos h5d_gcd
    omega

theorem coprime_test (n : ℕ) (hn : n > 0) :
    let d := Nat.gcd n 10000
    let u := n / d
    d < 10 → Nat.gcd u 100 = 1 := by
  intro d u h_lt
  have h_gcd_10 := gcd_u_10_eq_one n hn h_lt
  have h_coprime : Nat.Coprime u 10 := h_gcd_10
  have h_coprime2 : Nat.Coprime u (10^2) := Nat.Coprime.pow_right 2 h_coprime
  exact h_coprime2
