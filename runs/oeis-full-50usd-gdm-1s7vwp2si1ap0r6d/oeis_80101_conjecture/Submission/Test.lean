import FormalConjectures.Util.ProblemImports

open Nat Finset


lemma n_eq_of_nth_eq (n : ℕ) (hn : 0 < n) (k : ℕ) (h : Nat.nth Nat.Prime (n - 1) = Nat.nth Nat.Prime k) : n = k + 1 := by
  have h_eq : n - 1 = k := Nat.nth_injective Nat.infinite_setOf_prime h
  omega

lemma not_IsPrimePow_of_two_prime_divisors (n : ℕ) (p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hd1 : p1 ∣ n) (hd2 : p2 ∣ n) (hne : p1 ≠ p2) : ¬ IsPrimePow n := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, rfl⟩
  have hd1' : p1 ∣ p := hp1.dvd_of_dvd_pow hd1
  have hd2' : p2 ∣ p := hp2.dvd_of_dvd_pow hd2
  have heq1 : p = p1 := (hp.dvd_iff_eq hp1.ne_one).mp hd1'
  have heq2 : p = p2 := (hp.dvd_iff_eq hp2.ne_one).mp hd2'
  subst heq1 heq2
  exact hne rfl


lemma odd_prime_power_ge_121 (P q u : ℕ) (hP : 83 ≤ P) (hq : q.Prime) (hu : 2 ≤ u) (hq_ge3 : 3 ≤ q) (h_gt : P < q ^ u) : 121 ≤ q ^ u := by
  rcases le_or_gt 11 q with hq11 | hq11
  · -- q ≥ 11
    have hq_sq : 121 ≤ q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hq11 hq11
    have : q ^ 2 ≤ q ^ u := Nat.pow_le_pow_right (by omega) hu
    omega
  · -- q < 11
    have hq_cases : q = 3 ∨ q = 5 ∨ q = 7 := by
      interval_cases q <;> { try { revert hq; decide }; try { decide } }
    rcases hq_cases with rfl | rfl | rfl
    · -- q = 3
      have hu_ge5 : 5 ≤ u := by
        by_contra hc
        have : u ≤ 4 := by omega
        have : 3 ^ u ≤ 81 := by
          interval_cases u
          · decide
          · decide
          · decide
        omega
      calc 121 ≤ 243 := by decide
           _ ≤ 3 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 3) hu_ge5
    · -- q = 5
      have hu_ge3 : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 5 ^ u ≤ 25 := by
          interval_cases u
          · decide
        omega
      calc 121 ≤ 125 := by decide
           _ ≤ 5 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 5) hu_ge3
    · -- q = 7
      have hu_ge3 : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 7 ^ u ≤ 49 := by
          interval_cases u
          · decide
        omega
      calc 121 ≤ 343 := by decide
           _ ≤ 7 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 7) hu_ge3


lemma test_rcases (n : ℕ) (hn : 0 < n) (h_or : n - 1 = 10 ∨ n - 1 = 11 ∨ n - 1 = 12) : n = 11 ∨ n = 12 ∨ n = 13 := by
  rcases h_or with h | h | h
  · have h_eq : n = 11 := by omega
    subst h_eq
    left; rfl
  · have h_eq : n = 12 := by omega
    subst h_eq
    right; left; rfl
  · have h_eq : n = 13 := by omega
    subst h_eq
    right; right; rfl













lemma prime_ge_127_of_ge_124 (p : ℕ) (hp : p.Prime) (h : 124 ≤ p) : 127 ≤ p := by
  by_contra hc
  push_neg at hc
  interval_cases p <;> { revert hp; decide }

