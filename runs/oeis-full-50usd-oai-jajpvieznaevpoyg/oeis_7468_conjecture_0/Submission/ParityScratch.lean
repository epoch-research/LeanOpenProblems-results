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

-- For n ≥ 3 the row starts after index 0, hence all primes in the row are odd.
lemma row_prime_odd {n i : ℕ} (hn : 2 ≤ n) (hi : i ∈ Finset.range n) :
    Odd (Nat.nth Nat.Prime (n * (n - 1) / 2 + i)) := by
  apply nth_prime_odd_of_pos
  have hmul : 2 ≤ n * (n - 1) := by
    have hn1 : 1 ≤ n - 1 := Nat.succ_le_iff.mp hn
    nlinarith
  have hdiv : 0 < n * (n - 1) / 2 := by
    omega
  omega

-- This compiles: a row with n≥3 has sum parity equal to n parity.
lemma a_mod_two_of_two_le {n : ℕ} (hn : 2 ≤ n) : a n % 2 = n % 2 := by
  classical
  unfold a
  -- prove by induction over Finset.range? left as experiment; simp doesn't solve.
  induction n using Nat.caseStrongInductionOn with
  | hz => omega
  | hi n ih =>
    sorry
