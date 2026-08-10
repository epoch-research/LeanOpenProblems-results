import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A247824: Least positive integer $m$ such that $m + n$ divides $\mathrm{prime}(m) + \mathrm{prime}(n)$.
Here $\mathrm{prime}(k)$ denotes the $k$-th prime number, with $\mathrm{prime}(1) = 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  sInf { m : ℕ | m > 0 ∧ (m + n) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime (n - 1)) }

/--
Conjecture: a(n) exists for any n > 0. Moreover, a(n) < n*(n-1) for all n > 2. - _Zhi-Wei Sun_, Sep 25 2014
The existence of $a(n)$ for $n > 0$ is formalized as the non-emptiness of the set used in the definition of $\mathrm{sInf}$, which guarantees a positive least element exists.
-/
theorem oeis_247824_conjecture_0 :
  (∀ n : ℕ, 0 < n →
    ({ m : ℕ | 0 < m ∧ (m + n) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime (n - 1)) }).Nonempty)
  ∧
  (∀ n : ℕ, 2 < n → a n < n * (n - 1)) := by
  constructor
  · intro n hn
    rcases eq_or_ne n 1 with rfl | hn1
    · -- n = 1
      use 1
      simp [nth_prime_zero_eq_two]
    · rcases eq_or_ne n 2 with rfl | hn2
      · -- n = 2
        use 5
        simp [nth_prime_four_eq_eleven, nth_prime_one_eq_three]
      · rcases eq_or_ne n 3 with rfl | hn3
        · -- n = 3
          use 5
          simp [nth_prime_four_eq_eleven, nth_prime_two_eq_five]
        · rcases eq_or_ne n 4 with rfl | hn4
          · -- n = 4
            use 5
            simp [nth_prime_four_eq_eleven, nth_prime_three_eq_seven]
          · rcases eq_or_ne n 5 with rfl | hn5
            · -- n = 5
              use 2
              simp [nth_prime_one_eq_three, nth_prime_four_eq_eleven]
            · -- n > 5
              sorry
  · intro n hn
    rcases eq_or_ne n 3 with rfl | hn3
    · -- n = 3
      have ha3 : a 3 = sInf { m : ℕ | m > 0 ∧ (m + 3) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime 2) } := by
        unfold a
        simp
      rw [ha3]
      have h5 : 5 ∈ { m : ℕ | m > 0 ∧ (m + 3) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime 2) } := by
        simp [nth_prime_four_eq_eleven, nth_prime_two_eq_five]
      have hle := Nat.sInf_le h5
      omega
    · rcases eq_or_ne n 4 with rfl | hn4
      · -- n = 4
        have ha4 : a 4 = sInf { m : ℕ | m > 0 ∧ (m + 4) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime 3) } := by
          unfold a
          simp
        rw [ha4]
        have h5 : 5 ∈ { m : ℕ | m > 0 ∧ (m + 4) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime 3) } := by
          simp [nth_prime_four_eq_eleven, nth_prime_three_eq_seven]
        have hle := Nat.sInf_le h5
        omega
      · rcases eq_or_ne n 5 with rfl | hn5
        · -- n = 5
          have ha5 : a 5 = sInf { m : ℕ | m > 0 ∧ (m + 5) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime 4) } := by
            unfold a
            simp
          rw [ha5]
          have h2 : 2 ∈ { m : ℕ | m > 0 ∧ (m + 5) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime 4) } := by
            simp [nth_prime_one_eq_three, nth_prime_four_eq_eleven]
          have hle := Nat.sInf_le h2
          omega
        · -- n > 5
          sorry
