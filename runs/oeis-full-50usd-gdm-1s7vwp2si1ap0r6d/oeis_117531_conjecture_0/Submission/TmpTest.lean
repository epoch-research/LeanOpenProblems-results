import FormalConjectures.Util.ProblemImports

open Nat

lemma minFac_odd (n : ℕ) (hn : n % 2 = 1) : minFac n % 2 = 1 := by
  by_contra h
  have h_even : minFac n % 2 = 0 := by omega
  have h_dvd : 2 ∣ minFac n := Nat.dvd_of_mod_eq_zero h_even
  have h_dvd_n : minFac n ∣ n := minFac_dvd n
  have h_2_dvd_n : 2 ∣ n := dvd_trans h_dvd h_dvd_n
  have hn_even : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_2_dvd_n
  omega

lemma test_alg (k : ℕ) (hk : k ≥ 2) : (2 * k - 1) ^ 2 = 4 * (k ^ 2 - k) + 1 := by
  have h1 : 1 ≤ 2 * k := by omega
  have h2 : k ≤ k ^ 2 := by
    have : k ^ 2 = k * k := by ring
    rw [this]
    exact Nat.le_mul_self k
  zify [h1, h2]
  ring

lemma not_dvd_4_of_odd_prime (q : ℕ) (hp : Nat.Prime q) (ho : q % 2 = 1) : ¬ q ∣ 4 := by
  intro hd
  have hq_le : q ≤ 4 := Nat.le_of_dvd (by decide) hd
  have hq_ge : q ≥ 2 := hp.two_le
  rcases (by omega : q = 2 ∨ q = 3 ∨ q = 4) with rfl | rfl | rfl
  · omega
  · revert hd; decide
  · omega

lemma nth_prime_le_of_lt {m : ℕ} {p : ℕ} (hp : Nat.Prime p) (h_lt : Nat.nth Nat.Prime m < p) :
    Nat.nth Nat.Prime (m + 1) ≤ p := by
  have hm_prime : Nat.Prime (Nat.nth Nat.Prime m) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime m
  have h_count := Nat.count_strict_mono hm_prime h_lt
  have h_count_m : Nat.count Nat.Prime (Nat.nth Nat.Prime m) = m :=
    Nat.count_nth_of_infinite Nat.infinite_setOf_prime m
  rw [h_count_m] at h_count
  have h_le : m + 1 ≤ Nat.count Nat.Prime p := h_count
  have h_nth_le := (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone h_le
  have h_nth_count : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  exact _root_.trans h_nth_le h_nth_count.le

lemma nth_prime_le_pow (j : ℕ) : Nat.nth Nat.Prime j ≤ 2 ^ (j + 1) := by
  induction j with
  | zero =>
    simp
  | succ j ih =>
    have h_nz : Nat.nth Nat.Prime j ≠ 0 := by
      have : Nat.nth Nat.Prime j ≥ 2 := (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j).two_le
      omega
    have h_bertrand := Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime j) h_nz
    rcases h_bertrand with ⟨p, hp_prime, h_lt, h_le⟩
    have h_next_le : Nat.nth Nat.Prime (j + 1) ≤ p := nth_prime_le_of_lt hp_prime h_lt
    have h_p_le : p ≤ 2 * 2 ^ (j + 1) := by omega
    have h_pow : 2 * 2 ^ (j + 1) = 2 ^ (j + 2) := by ring
    omega

lemma helper_composite_witness (p : ℕ) (hp : Nat.Prime p) (h_comp : ¬ Nat.Prime (4*p - 1)) (hp_ge : p ≥ 43) :
    ∃ k, k ≥ 2 ∧ k^2 - k < p ∧ ¬ Nat.Prime (k^2 - k + p) := by
  have hP_pos : 0 < 4 * p - 1 := by omega
  have hP_ne1 : 4 * p - 1 ≠ 1 := by omega
  let q := minFac (4 * p - 1)
  have hq_prime : Nat.Prime q := minFac_prime hP_ne1
  have hq_dvd : q ∣ 4 * p - 1 := minFac_dvd (4 * p - 1)
  have hq_sq_le : q^2 ≤ 4 * p - 1 := minFac_sq_le_self hP_pos h_comp
  have h_odd : (4 * p - 1) % 2 = 1 := by omega
  have hq_odd : q % 2 = 1 := minFac_odd (4 * p - 1) h_odd
  have hq_ge2 : q ≥ 2 := hq_prime.two_le
  have hq_ge3 : q ≥ 3 := by omega
  let k := (q + 1) / 2
  have hk_ge2 : k ≥ 2 := by omega
  have hq_eq : 2 * k - 1 = q := by omega
  have h_alg : (2 * k - 1) ^ 2 = 4 * (k ^ 2 - k) + 1 := by
    have h1 : 1 ≤ 2 * k := by omega
    have h2 : k ≤ k ^ 2 := by
      have : k ^ 2 = k * k := by ring
      rw [this]
      exact Nat.le_mul_self k
    zify [h1, h2]
    ring
  have h_alg2 : q ^ 2 + (4 * p - 1) = 4 * (k ^ 2 - k + p) := by
    rw [← hq_eq, h_alg]
    have h_sub1 : 1 ≤ 4 * p := by omega
    have h_sub2 : k ≤ k ^ 2 := by
      have : k ^ 2 = k * k := by ring
      rw [this]
      exact Nat.le_mul_self k
    zify [h_sub1, h_sub2]
    ring
  have h_p_sq_ge : p ^ 2 ≥ 4 * p := by
    have : p ^ 2 = p * p := by ring
    rw [this]
    have : p ≥ 4 := by omega
    exact Nat.mul_le_mul_right p this
  have h_q_sq_lt_p_sq : q ^ 2 < p ^ 2 := by
    have h_lt : q ^ 2 < 4 * p := by omega
    omega
  have hq_lt_p : q < p := by
    by_contra! h_le
    have h_sq_ge := Nat.mul_self_le_mul_self h_le
    have hq_sq_eq : q ^ 2 = q * q := by ring
    have hp_sq_eq : p ^ 2 = p * p := by ring
    rw [hq_sq_eq, hp_sq_eq] at h_q_sq_lt_p_sq
    omega
  have h_k2_lt_p : k ^ 2 - k < p := by
    have h_step : (2 * k - 1) ^ 2 ≤ 4 * p - 1 := by
      rw [← hq_eq] at hq_sq_le
      exact hq_sq_le
    rw [h_alg] at h_step
    omega
  use k
  refine ⟨hk_ge2, h_k2_lt_p, ?_⟩
  have h_dvd_mul : q ∣ 4 * (k ^ 2 - k + p) := by
    rw [← h_alg2]
    have hq_dvd_sq : q ∣ q ^ 2 := by
      have : q ^ 2 = q * q := by ring
      rw [this]
      exact dvd_mul_right q q
    exact dvd_add hq_dvd_sq hq_dvd
  have h_or : q ∣ 4 ∨ q ∣ k ^ 2 - k + p := hq_prime.prime.dvd_mul.mp h_dvd_mul
  have h_not_dvd_4 : ¬ q ∣ 4 := not_dvd_4_of_odd_prime q hq_prime hq_odd
  have hq_dvd_k2_k_p : q ∣ k ^ 2 - k + p := h_or.resolve_left h_not_dvd_4
  have h_lt : q < k ^ 2 - k + p := by omega
  have hq_ge2 : 2 ≤ q := hq_prime.two_le
  exact Nat.not_prime_of_dvd_of_lt hq_dvd_k2_k_p hq_ge2 h_lt
