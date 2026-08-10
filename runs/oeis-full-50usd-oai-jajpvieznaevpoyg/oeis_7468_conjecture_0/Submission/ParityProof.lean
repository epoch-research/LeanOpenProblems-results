import FormalConjectures.Util.ProblemImports

lemma nth_prime_ne_two_of_pos {k : ℕ} (hk : 0 < k) : Nat.nth Nat.Prime k ≠ 2 := by
  have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime k :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime) hk
  rw [Nat.nth_prime_zero_eq_two] at hlt
  omega

lemma nth_prime_odd_of_pos {k : ℕ} (hk : 0 < k) : Odd (Nat.nth Nat.Prime k) := by
  exact (Nat.prime_nth_prime k).odd_of_ne_two (nth_prime_ne_two_of_pos hk)

#check nth_prime_odd_of_pos
