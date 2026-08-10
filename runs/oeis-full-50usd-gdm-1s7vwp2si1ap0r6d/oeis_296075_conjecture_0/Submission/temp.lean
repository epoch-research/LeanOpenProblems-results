import Mathlib

open Nat

lemma divisors_prime_sq {d : ℕ} (hd : d.Prime) : divisors (d^2) = {1, d, d^2} := by
  ext x
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h_dvd
    obtain ⟨hx_dvd, _⟩ := h_dvd
    rw [Nat.dvd_prime_pow hd] at hx_dvd
    obtain ⟨j, hk_le, rfl⟩ := hx_dvd
    interval_cases j
    · left; rfl
    · right; left; ring
    · right; right; ring
  · rintro (rfl | rfl | rfl)
    · exact ⟨Nat.one_dvd _, pow_ne_zero 2 hd.ne_zero⟩
    · exact ⟨dvd_pow_self _ (by decide), pow_ne_zero 2 hd.ne_zero⟩
    · exact ⟨dvd_rfl, pow_ne_zero 2 hd.ne_zero⟩

theorem test_div2 (p d : ℕ) (hp : p.Prime) (hd : d.Prime) (hpd : p ≠ d) : divisors (p * d^2) = {1, p, d, p * d, d^2, p * d^2} := by
  rw [Nat.divisors_mul, hp.divisors, divisors_prime_sq hd]
  ext x
  rw [Finset.mem_mul]
  simp
  omega

theorem test_prop_sum (p d : ℕ) (hp : p.Prime) (hd : d.Prime) (hpd : p < d) :
    ({1, p, d, p * d, d^2} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = p + 2 * d + 4 := by
  have hgp : p ≥ 2 := hp.two_le
  have hgd : d ≥ 3 := by omega
  have hp_ne1 : 1 ≠ p := hp.ne_one.symm
  have hd_ne1 : 1 ≠ d := hd.ne_one.symm
  have hpd_ne1 : 1 ≠ p * d := by
    nlinarith
  have hd2_ne1 : 1 ≠ d^2 := by
    nlinarith
  have hp_ne_d : p ≠ d := hpd.ne
  have hp_ne_pd : p ≠ p * d := by
    nlinarith
  have hp_ne_d2 : p ≠ d^2 := by
    nlinarith
  have hd_ne_pd : d ≠ p * d := by
    nlinarith
  have hd_ne_d2 : d ≠ d^2 := by
    nlinarith
  have hpd_ne_d2 : p * d ≠ d^2 := by
    have : p * d < d^2 := by
      nlinarith
    omega
  have h_sum5 : ({1, p, d, p * d, d^2} : Finset ℕ).sum (fun x => (ArithmeticFunction.sigma 1 x : ℤ) - x) =
      ((ArithmeticFunction.sigma 1 1 : ℤ) - 1) + ((ArithmeticFunction.sigma 1 p : ℤ) - p) +
      ((ArithmeticFunction.sigma 1 d : ℤ) - d) + ((ArithmeticFunction.sigma 1 (p * d) : ℤ) - p * d) +
      ((ArithmeticFunction.sigma 1 (d^2) : ℤ) - d^2) := by
    have h1 : 1 ∉ (insert p (insert d (insert (p * d) {d^2})) : Finset ℕ) := by
      simp [hp_ne1, hd_ne1, hpd_ne1, hd2_ne1]
    have h2 : p ∉ (insert d (insert (p * d) {d^2}) : Finset ℕ) := by
      simp [hp_ne_d, hp_ne_pd, hp_ne_d2]
    have h3 : d ∉ (insert (p * d) {d^2} : Finset ℕ) := by
      simp [hd_ne_pd, hd_ne_d2]
    have h4 : p * d ∉ ({d^2} : Finset ℕ) := by
      simp [hpd_ne_d2]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    rw [Finset.sum_insert h3]
    rw [Finset.sum_insert h4]
    simp
    ring
  have h_sigma1_1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
  have h_sigma1_p : (ArithmeticFunction.sigma 1 p : ℤ) = p + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors p, (c : ℤ) ^ 1) = ∑ c ∈ divisors p, (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow, hp.divisors]
    rw [Finset.sum_pair hp_ne1]
    ring
  have h_sigma1_d : (ArithmeticFunction.sigma 1 d : ℤ) = d + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors d, (c : ℤ) ^ 1) = ∑ c ∈ divisors d, (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow, hd.divisors]
    rw [Finset.sum_pair hd_ne1]
    ring
  have h_sigma1_pd : (ArithmeticFunction.sigma 1 (p * d) : ℤ) = p * d + p + d + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors (p * d), (c : ℤ) ^ 1) = ∑ c ∈ divisors (p * d), (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    have h_div_pd : divisors (p * d) = {1, p, d, p * d} := by
      rw [Nat.divisors_mul, hp.divisors, hd.divisors]
      ext x
      rw [Finset.mem_mul]
      simp
      omega
    rw [h_div_pd]
    have h1 : 1 ∉ (insert p (insert d {p * d}) : Finset ℕ) := by
      simp [hp_ne1, hd_ne1, hpd_ne1]
    have h2 : p ∉ (insert d {p * d} : Finset ℕ) := by
      simp [hp_ne_d, hp_ne_pd]
    have h3 : d ∉ ({p * d} : Finset ℕ) := by
      simp [hd_ne_pd]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    rw [Finset.sum_insert h3]
    simp
    ring
  have h_sigma1_d2 : (ArithmeticFunction.sigma 1 (d^2) : ℤ) = d^2 + d + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors (d^2), (c : ℤ) ^ 1) = ∑ c ∈ divisors (d^2), (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow, divisors_prime_sq hd]
    have h1 : 1 ∉ (insert d {d^2} : Finset ℕ) := by
      simp [hd_ne1, hd2_ne1]
    have h2 : d ∉ ({d^2} : Finset ℕ) := by
      simp [hd_ne_d2]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    simp
    ring
  rw [h_sum5]
  rw [h_sigma1_1, h_sigma1_p, h_sigma1_d, h_sigma1_pd, h_sigma1_d2]
  ring
