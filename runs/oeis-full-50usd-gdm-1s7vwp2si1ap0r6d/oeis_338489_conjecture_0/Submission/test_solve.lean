import FormalConjectures.Util.ProblemImports
open Nat

lemma exists_prime_div_factorial (n : ℕ) (hn : 6 ≤ n) : ∃ p, Nat.Prime p ∧ n / 2 < p ∧ p ≤ n := by
  have h_pos : n / 2 ≠ 0 := by omega
  obtain ⟨p, hp_prime, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) h_pos
  use p
  refine ⟨hp_prime, hp1, ?_⟩
  have h_le : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  exact hp2.trans h_le

lemma factorial_gt_quadratic {n : ℕ} (hn : 4 ≤ n) : 2 * n.factorial > n * (n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · -- Prove 2 * (m + 1)! > (m + 1) * (m + 2)
    rw [factorial_succ]
    -- 2 * (m + 1) * m.factorial = (m + 1) * (2 * m.factorial)
    have h_mul : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by ring
    rw [h_mul]
    have h1 : 2 * m.factorial > m * (m + 1) := ih
    have h2 : (m + 1) * (2 * m.factorial) > (m + 1) * (m * (m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left h1 (by omega)
    have h3 : m * (m + 1) ≥ m + 2 := by
      calc m * (m + 1) ≥ 4 * (m + 1) := Nat.mul_le_mul_right (m + 1) hm
        _ = 4 * m + 4 := by ring
        _ ≥ m + 2 := by omega
    have h4 : (m + 1) * (m * (m + 1)) ≥ (m + 1) * (m + 2) := Nat.mul_le_mul_left (m + 1) h3
    exact lt_of_le_of_lt h4 h2

lemma k_ge_two_p {n k p : ℕ} (h_eq : 2 * n.factorial = k * (k + 1))
    (hp_prime : Nat.Prime p) (hp_gt : n / 2 < p) (hp_le : p ≤ n) (hn : 61 ≤ n) :
    k + 1 ≥ 2 * p := by
  have hp_dvd_fact : p ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hp_prime) hp_le
  have hp_dvd_two_fact : p ∣ 2 * n.factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
  rw [← h_eq]
  rw [h_eq] at hp_dvd_two_fact
  cases' Nat.Prime.dvd_mul hp_prime |>.mp hp_dvd_two_fact with hpk hpk1
  · obtain ⟨d, hd⟩ := hpk
    have hd_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      have hk0 : k = 0 := by omega
      rw [hk0] at h_eq
      simp at h_eq
      have h_fact_pos : n.factorial > 0 := Nat.factorial_pos n
      omega
    rcases eq_or_ne d 1 with rfl | hd_ne
    · have hkp : k = p := by omega
      rw [hkp] at h_eq
      have hp_le_fact : p * (p + 1) ≤ n * (n + 1) := Nat.mul_le_mul hp_le (by omega)
      have h_gt : 2 * n.factorial > n * (n + 1) := factorial_gt_quadratic (by omega)
      omega
    · have hd_ge_2 : d ≥ 2 := by omega
      have hk_ge : k ≥ 2 * p := by
        calc k = p * d := hd
          _ ≥ p * 2 := Nat.mul_le_mul_left p hd_ge_2
          _ = 2 * p := by ring
      omega
  · obtain ⟨d, hd⟩ := hpk1
    have hd_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      have hk1 : k + 1 = 0 := by omega
      omega
    rcases eq_or_ne d 1 with rfl | hd_ne
    · have hkp : k + 1 = p := by omega
      have hk_eq : k = p - 1 := by omega
      rw [hk_eq, hkp] at h_eq
      have hp_le_fact : (p - 1) * p ≤ (n - 1) * n := by
        have h_p_pos : p > 0 := Nat.Prime.pos hp_prime
        have h_sub : p - 1 ≤ n - 1 := by omega
        exact Nat.mul_le_mul h_sub hp_le
      have h_gt : 2 * n.factorial > n * (n - 1) := by
        have h_gt_quad : 2 * n.factorial > n * (n + 1) := factorial_gt_quadratic (by omega)
        have h_quad_le : n * (n + 1) ≥ (n - 1) * n := by
          have : n + 1 ≥ n - 1 := by omega
          have h_mul_comm : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
          rw [h_mul_comm]
          exact Nat.mul_le_mul_left n this
        omega
      have h_comm : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
      rw [h_comm] at hp_le_fact
      omega
    · have hd_ge_2 : d ≥ 2 := by omega
      calc k + 1 = p * d := hd
        _ ≥ p * 2 := Nat.mul_le_mul_left p hd_ge_2
        _ = 2 * p := by ring


lemma factorial_gt_two_n_mul {n : ℕ} (hn : 5 ≤ n) : 2 * n.factorial ≥ 2 * n * (2 * n - 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · rw [factorial_succ]
    -- 2 * (m + 1)! = 2 * (m + 1) * m! = (m + 1) * (2 * m!)
    have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by ring
    rw [h_eq]
    have ih' : 2 * m.factorial ≥ 2 * m * (2 * m - 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) ≥ (m + 1) * (2 * m * (2 * m - 1)) := Nat.mul_le_mul_left (m + 1) ih'
    have h2 : (m + 1) * (2 * m * (2 * m - 1)) ≥ 2 * (m + 1) * (2 * (m + 1) - 1) := by
      have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [this]
      -- Prove (m + 1) * 2 * m * (2 * m - 1) >= 2 * (m + 1) * (2 * m + 1)
      -- which is 2 * (m + 1) * m * (2 * m - 1) >= 2 * (m + 1) * (2 * m + 1)
      -- which is m * (2 * m - 1) >= 2 * m + 1
      -- m * (2 * m - 1) = 2 * m^2 - m
      -- since m >= 5, 2 * m^2 - m >= 2 * m + 1 is true
      have h3 : m * (2 * m - 1) ≥ 2 * m + 1 := by
        calc m * (2 * m - 1) = 2 * m * m - m := by ring
          _ ≥ 2 * 5 * m - m := by
            have : 2 * m * m ≥ 2 * 5 * m := Nat.mul_le_mul_left (2 * m) hm
            -- wait, 2*m*m = 2*m*m, and m >= 5 so 2*m*m >= 10*m
            omega
          _ = 9 * m := by ring
          _ ≥ 2 * m + m := by omega
          _ ≥ 2 * m + 5 := by omega
          _ ≥ 2 * m + 1 := by omega
      have h4 : 2 * (m + 1) * (m * (2 * m - 1)) ≥ 2 * (m + 1) * (2 * m + 1) := Nat.mul_le_mul_left (2 * (m + 1)) h3
      -- we have (m + 1) * (2 * m * (2 * m - 1)) = 2 * (m + 1) * (m * (2 * m - 1))
      have h_comm : (m + 1) * (2 * m * (2 * m - 1)) = 2 * (m + 1) * (m * (2 * m - 1)) := by ring
      rw [h_comm]
      exact h4
    exact le_trans h2 h1

lemma k_ge_two_n {n k : ℕ} (h_eq : 2 * n.factorial = k * (k + 1)) (hn : 5 ≤ n) : k + 1 ≥ 2 * n := by
  by_contra hc
  have hk : k + 1 < 2 * n := by omega
  have hk2 : k < 2 * n - 1 := by omega
  have h_lt : k * (k + 1) < 2 * n * (2 * n - 1) := by
    -- Since k < 2 * n - 1 and k + 1 < 2 * n
    have : k * (k + 1) < (2 * n - 1) * (2 * n) := Nat.mul_lt_mul hk2 (by omega) (by omega)
    rw [Nat.mul_comm (2 * n - 1) (2 * n)] at this
    exact this
  have h_ge : 2 * n.factorial ≥ 2 * n * (2 * n - 1) := factorial_gt_two_n_mul hn
  omega


def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

lemma is_triangular_iff_dec (x : ℕ) : is_triangular x ↔ (List.range (2 * x + 2)).any (fun k => x == k * (k + 1) / 2) = true := by
  sorry

theorem not_triangular_6 : ¬ is_triangular (factorial 6) := by sorry
theorem not_triangular_7 : ¬ is_triangular (factorial 7) := by sorry
theorem not_triangular_8 : ¬ is_triangular (factorial 8) := by sorry
theorem not_triangular_9 : ¬ is_triangular (factorial 9) := by sorry
theorem not_triangular_10 : ¬ is_triangular (factorial 10) := by sorry
theorem not_triangular_11 : ¬ is_triangular (factorial 11) := by sorry
theorem not_triangular_12 : ¬ is_triangular (factorial 12) := by sorry
theorem not_triangular_13 : ¬ is_triangular (factorial 13) := by sorry
theorem not_triangular_14 : ¬ is_triangular (factorial 14) := by sorry
theorem not_triangular_15 : ¬ is_triangular (factorial 15) := by sorry
theorem not_triangular_16 : ¬ is_triangular (factorial 16) := by sorry
theorem not_triangular_17 : ¬ is_triangular (factorial 17) := by sorry
theorem not_triangular_18 : ¬ is_triangular (factorial 18) := by sorry
theorem not_triangular_19 : ¬ is_triangular (factorial 19) := by sorry
theorem not_triangular_20 : ¬ is_triangular (factorial 20) := by sorry
theorem not_triangular_21 : ¬ is_triangular (factorial 21) := by sorry
theorem not_triangular_22 : ¬ is_triangular (factorial 22) := by sorry
theorem not_triangular_23 : ¬ is_triangular (factorial 23) := by sorry
theorem not_triangular_24 : ¬ is_triangular (factorial 24) := by sorry
theorem not_triangular_25 : ¬ is_triangular (factorial 25) := by sorry
theorem not_triangular_26 : ¬ is_triangular (factorial 26) := by sorry
theorem not_triangular_27 : ¬ is_triangular (factorial 27) := by sorry
theorem not_triangular_28 : ¬ is_triangular (factorial 28) := by sorry
theorem not_triangular_29 : ¬ is_triangular (factorial 29) := by sorry
theorem not_triangular_30 : ¬ is_triangular (factorial 30) := by sorry
theorem not_triangular_31 : ¬ is_triangular (factorial 31) := by sorry
theorem not_triangular_32 : ¬ is_triangular (factorial 32) := by sorry
theorem not_triangular_33 : ¬ is_triangular (factorial 33) := by sorry
theorem not_triangular_34 : ¬ is_triangular (factorial 34) := by sorry
theorem not_triangular_35 : ¬ is_triangular (factorial 35) := by sorry
theorem not_triangular_36 : ¬ is_triangular (factorial 36) := by sorry
theorem not_triangular_37 : ¬ is_triangular (factorial 37) := by sorry
theorem not_triangular_38 : ¬ is_triangular (factorial 38) := by sorry
theorem not_triangular_39 : ¬ is_triangular (factorial 39) := by sorry
theorem not_triangular_40 : ¬ is_triangular (factorial 40) := by sorry
theorem not_triangular_41 : ¬ is_triangular (factorial 41) := by sorry
theorem not_triangular_42 : ¬ is_triangular (factorial 42) := by sorry
theorem not_triangular_43 : ¬ is_triangular (factorial 43) := by sorry
theorem not_triangular_44 : ¬ is_triangular (factorial 44) := by sorry
theorem not_triangular_45 : ¬ is_triangular (factorial 45) := by sorry
theorem not_triangular_46 : ¬ is_triangular (factorial 46) := by sorry
theorem not_triangular_47 : ¬ is_triangular (factorial 47) := by sorry
theorem not_triangular_48 : ¬ is_triangular (factorial 48) := by sorry
theorem not_triangular_49 : ¬ is_triangular (factorial 49) := by sorry
theorem not_triangular_50 : ¬ is_triangular (factorial 50) := by sorry
theorem not_triangular_51 : ¬ is_triangular (factorial 51) := by sorry
theorem not_triangular_52 : ¬ is_triangular (factorial 52) := by sorry
theorem not_triangular_53 : ¬ is_triangular (factorial 53) := by sorry
theorem not_triangular_54 : ¬ is_triangular (factorial 54) := by sorry
theorem not_triangular_55 : ¬ is_triangular (factorial 55) := by sorry
theorem not_triangular_56 : ¬ is_triangular (factorial 56) := by sorry
theorem not_triangular_57 : ¬ is_triangular (factorial 57) := by sorry
theorem not_triangular_58 : ¬ is_triangular (factorial 58) := by sorry
theorem not_triangular_59 : ¬ is_triangular (factorial 59) := by sorry
theorem not_triangular_60 : ¬ is_triangular (factorial 60) := by sorry

lemma not_triangular_of_ge_61 {n : ℕ} (hn : 61 ≤ n) : ¬ is_triangular n.factorial := by
  sorry

theorem oeis_338489_conjecture_0_test :
    ∀ n : ℕ, is_triangular n.factorial ↔ n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 5 := by
  intro n
  constructor
  · intro h
    rcases lt_or_ge n 6 with hn | hn
    · interval_cases n
      · left; rfl
      · right; left; rfl
      · rw [is_triangular_iff_dec] at h
        revert h; decide
      · right; right; left; rfl
      · rw [is_triangular_iff_dec] at h
        revert h; decide
      · right; right; right; rfl
    · rcases lt_or_ge n 61 with hn_lt | hn_ge
      · interval_cases n
        · exfalso; exact not_triangular_6 h
        · exfalso; exact not_triangular_7 h
        · exfalso; exact not_triangular_8 h
        · exfalso; exact not_triangular_9 h
        · exfalso; exact not_triangular_10 h
        · exfalso; exact not_triangular_11 h
        · exfalso; exact not_triangular_12 h
        · exfalso; exact not_triangular_13 h
        · exfalso; exact not_triangular_14 h
        · exfalso; exact not_triangular_15 h
        · exfalso; exact not_triangular_16 h
        · exfalso; exact not_triangular_17 h
        · exfalso; exact not_triangular_18 h
        · exfalso; exact not_triangular_19 h
        · exfalso; exact not_triangular_20 h
        · exfalso; exact not_triangular_21 h
        · exfalso; exact not_triangular_22 h
        · exfalso; exact not_triangular_23 h
        · exfalso; exact not_triangular_24 h
        · exfalso; exact not_triangular_25 h
        · exfalso; exact not_triangular_26 h
        · exfalso; exact not_triangular_27 h
        · exfalso; exact not_triangular_28 h
        · exfalso; exact not_triangular_29 h
        · exfalso; exact not_triangular_30 h
        · exfalso; exact not_triangular_31 h
        · exfalso; exact not_triangular_32 h
        · exfalso; exact not_triangular_33 h
        · exfalso; exact not_triangular_34 h
        · exfalso; exact not_triangular_35 h
        · exfalso; exact not_triangular_36 h
        · exfalso; exact not_triangular_37 h
        · exfalso; exact not_triangular_38 h
        · exfalso; exact not_triangular_39 h
        · exfalso; exact not_triangular_40 h
        · exfalso; exact not_triangular_41 h
        · exfalso; exact not_triangular_42 h
        · exfalso; exact not_triangular_43 h
        · exfalso; exact not_triangular_44 h
        · exfalso; exact not_triangular_45 h
        · exfalso; exact not_triangular_46 h
        · exfalso; exact not_triangular_47 h
        · exfalso; exact not_triangular_48 h
        · exfalso; exact not_triangular_49 h
        · exfalso; exact not_triangular_50 h
        · exfalso; exact not_triangular_51 h
        · exfalso; exact not_triangular_52 h
        · exfalso; exact not_triangular_53 h
        · exfalso; exact not_triangular_54 h
        · exfalso; exact not_triangular_55 h
        · exfalso; exact not_triangular_56 h
        · exfalso; exact not_triangular_57 h
        · exfalso; exact not_triangular_58 h
        · exfalso; exact not_triangular_59 h
        · exfalso; exact not_triangular_60 h
      · exfalso; exact not_triangular_of_ge_61 hn_ge h
  · rintro (rfl | rfl | rfl | rfl)
    · use 1; rfl
    · use 1; rfl
    · use 3; rfl
    · use 15; rfl

