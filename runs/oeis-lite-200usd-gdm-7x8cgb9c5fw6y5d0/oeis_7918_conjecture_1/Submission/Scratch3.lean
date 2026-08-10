import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

lemma a_eq_self_of_prime (n : ℕ) (hn : Nat.Prime n) : a n = n := by
  rw [a]
  exact (Nat.find_eq_iff _).2 ⟨⟨hn, le_refl _⟩, fun m hm => by
    rintro ⟨h_prime, h_le⟩
    omega
  ⟩

lemma helper (n : ℕ) (hn : 1 < n) : (n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have hn_real : 1 < (n : ℝ) := by exact_mod_cast hn
  have h_lt : (1 : ℝ) < (n : ℝ) ^ (1 / (n : ℝ)) := by
    have h_div_pos : 0 < 1 / (n : ℝ) := by positivity
    have h_base_lt : (1 : ℝ) ^ (1 / (n : ℝ)) < (n : ℝ) ^ (1 / (n : ℝ)) := by
      exact Real.rpow_lt_rpow zero_le_one hn_real h_div_pos
    rw [Real.one_rpow] at h_base_lt
    exact h_base_lt
  have h_rpow_lt := Real.rpow_lt_rpow_of_exponent_lt hn_real h_lt
  rw [Real.rpow_one] at h_rpow_lt
  exact h_rpow_lt

theorem prime_case (n : ℕ) (hn : Nat.Prime n) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have ha : a n = n := a_eq_self_of_prime n hn
  rw [ha]
  exact helper n h_n

lemma a_lt_two_mul (n : ℕ) (hn : 1 < n) : a n < 2 * n := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨p, hp_prime, hp_lt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  have ha_le_p : a n ≤ p := by
    rw [a]
    exact Nat.find_min' _ ⟨hp_prime, hp_lt.le⟩
  have hp_lt_two : p < 2 * n := by
    -- we have hp_le : p <= 2 * n.
    -- since p is prime, can p = 2 * n?
    -- if p = 2 * n, then 2 divides p. Since p is prime, p must be 2.
    -- then 2 * n = 2, so n = 1. But hn : 1 < n, contradiction.
    by_cases h_eq : p = 2 * n
    · have h2 : 2 ∣ p := by
        rw [h_eq]
        exact dvd_mul_right 2 n
      have hp2 : p = 2 ∨ Odd p := hp_prime.eq_two_or_odd'
      have hp_not_odd : ¬ Odd p := by
        rw [h_eq]
        rintro ⟨k, hk⟩
        omega
      have hp2 : p = 2 := by tauto
      omega
    · omega
  omega
