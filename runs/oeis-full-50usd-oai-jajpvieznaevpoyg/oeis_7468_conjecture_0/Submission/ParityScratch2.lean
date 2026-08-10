import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

lemma nth_prime_ne_two_of_pos {k : ℕ} (hk : 0 < k) : Nat.nth Nat.Prime k ≠ 2 := by
  have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime k :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime) hk
  rw [Nat.nth_prime_zero_eq_two] at hlt
  omega

lemma nth_prime_odd_of_pos {k : ℕ} (hk : 0 < k) : Odd (Nat.nth Nat.Prime k) := by
  exact (Nat.prime_nth_prime k).odd_of_ne_two (nth_prime_ne_two_of_pos hk)

lemma row_prime_odd {n i : ℕ} (hn : 2 ≤ n) (hi : i ∈ Finset.range n) :
    Odd (Nat.nth Nat.Prime (n * (n - 1) / 2 + i)) := by
  apply nth_prime_odd_of_pos
  have hdiv : 0 < n * (n - 1) / 2 := by omega
  omega

example {n : ℕ} (hn : 2 ≤ n) : ∀ i ∈ Finset.range n,
    (Nat.nth Nat.Prime (n * (n - 1) / 2 + i)) % 2 = 1 := by
  intro i hi
  exact (row_prime_odd hn hi).mod_two_eq_one
