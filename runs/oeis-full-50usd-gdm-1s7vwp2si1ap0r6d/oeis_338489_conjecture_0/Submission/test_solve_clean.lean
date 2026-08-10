import FormalConjectures.Util.ProblemImports
open Nat

lemma factorial_gt_quadratic {n : ℕ} (hn : 4 ≤ n) : 2 * n.factorial > n * (n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_mul : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
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
    (hp_prime : Nat.Prime p) (hp_gt : n / 2 < p) (hp_le : p ≤ n) (hn : 67 ≤ n) :
    k + 1 ≥ 2 * p := by
  have hp_dvd_fact : p ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hp_prime) hp_le
  have hp_dvd_two_fact : p ∣ 2 * n.factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
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
      rw [hk_eq] at h_eq
      have hp_eq : p - 1 + 1 = p := by omega
      rw [hp_eq] at h_eq
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
