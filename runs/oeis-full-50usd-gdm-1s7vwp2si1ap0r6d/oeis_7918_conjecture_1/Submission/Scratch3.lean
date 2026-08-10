import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

theorem a_le_two_mul (n : ℕ) (h_n : 1 < n) : a n ≤ 2 * n := by
  have h_exists := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  rcases h_exists with ⟨p, hp, hn_lt, hp_le⟩
  have h_min : @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  ) ≤ p := by
    apply Nat.find_le
    exact ⟨hp, by omega⟩
  have h_a_def : a n = @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  ) := rfl
  rw [h_a_def]
  exact h_min.trans hp_le

theorem prime_a (n : ℕ) : Nat.Prime (a n) := by
  have h_a_def : a n = @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  ) := rfl
  rw [h_a_def]
  have h_ex : ∃ p, Nat.Prime p ∧ n ≤ p := by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  have h_spec := Nat.find_spec h_ex
  exact h_spec.1

theorem le_a (n : ℕ) : n ≤ a n := by
  have h_a_def : a n = @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  ) := rfl
  rw [h_a_def]
  have h_ex : ∃ p, Nat.Prime p ∧ n ≤ p := by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  have h_spec := Nat.find_spec h_ex
  exact h_spec.2

theorem a_ne_two_mul (n : ℕ) (h_n : 1 < n) : a n ≠ 2 * n := by
  intro h_eq
  have hp_a := prime_a n
  rw [h_eq] at hp_a
  have hdvd : 2 ∣ 2 * n := Nat.dvd_mul_right 2 n
  have h_cases := Nat.Prime.eq_one_or_self_of_dvd hp_a 2 hdvd
  rcases h_cases with h2_eq_1 | h2_eq_2n
  · contradiction
  · omega

theorem a_lt_two_mul (n : ℕ) (h_n : 1 < n) : a n < 2 * n := by
  have h_le := a_le_two_mul n h_n
  have h_ne := a_ne_two_mul n h_n
  exact lt_of_le_of_ne h_le h_ne

theorem a_le_two_mul_sub_one (n : ℕ) (h_n : 1 < n) : a n ≤ 2 * n - 1 := by
  have h_lt := a_lt_two_mul n h_n
  omega
