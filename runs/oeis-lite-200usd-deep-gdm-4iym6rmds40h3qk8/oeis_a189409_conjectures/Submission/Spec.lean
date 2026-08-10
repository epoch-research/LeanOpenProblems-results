import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

theorem nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by
  have hcount : Nat.count Nat.Prime 2 = 0 := rfl
  have hprime : Nat.Prime 2 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

theorem nth_prime_one : Nat.nth Nat.Prime 1 = 3 := by
  have hcount : Nat.count Nat.Prime 3 = 1 := rfl
  have hprime : Nat.Prime 3 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

theorem nth_prime_two : Nat.nth Nat.Prime 2 = 5 := by
  have hcount : Nat.count Nat.Prime 5 = 2 := rfl
  have hprime : Nat.Prime 5 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

theorem nth_prime_three : Nat.nth Nat.Prime 3 = 7 := by
  have hcount : Nat.count Nat.Prime 7 = 3 := rfl
  have hprime : Nat.Prime 7 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

theorem nth_prime_four : Nat.nth Nat.Prime 4 = 11 := by
  have hcount : Nat.count Nat.Prime 11 = 4 := rfl
  have hprime : Nat.Prime 11 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

theorem nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have hcount : Nat.count Nat.Prime 13 = 5 := rfl
  have hprime : Nat.Prime 13 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

theorem nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have hcount : Nat.count Nat.Prime 17 = 6 := rfl
  have hprime : Nat.Prime 17 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

theorem nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have hcount : Nat.count Nat.Prime 19 = 7 := rfl
  have hprime : Nat.Prime 19 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

theorem nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have hcount : Nat.count Nat.Prime 23 = 8 := rfl
  have hprime : Nat.Prime 23 := by decide
  have hnth := Nat.nth_count hprime
  rwa [hcount] at hnth

noncomputable def prod_primes : ℕ → ℕ
  | 0 => 1
  | n + 1 => prod_primes n * Nat.nth Nat.Prime n

theorem prod_primes_eq (n : ℕ) : (range n).prod (fun k => Nat.nth Nat.Prime k) = prod_primes n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    rfl

theorem prod_primes_nine_eq : prod_primes 9 = 223092870 := by
  change prod_primes 8 * Nat.nth Nat.Prime 8 = 223092870
  rw [nth_prime_eight]
  change (prod_primes 7 * Nat.nth Nat.Prime 7) * 23 = 223092870
  rw [nth_prime_seven]
  change ((prod_primes 6 * Nat.nth Nat.Prime 6) * 19) * 23 = 223092870
  rw [nth_prime_six]
  change (((prod_primes 5 * Nat.nth Nat.Prime 5) * 17) * 19) * 23 = 223092870
  rw [nth_prime_five]
  change ((((prod_primes 4 * Nat.nth Nat.Prime 4) * 13) * 17) * 19) * 23 = 223092870
  rw [nth_prime_four]
  change (((((prod_primes 3 * Nat.nth Nat.Prime 3) * 11) * 13) * 17) * 19) * 23 = 223092870
  rw [nth_prime_three]
  change ((((((prod_primes 2 * Nat.nth Nat.Prime 2) * 7) * 11) * 13) * 17) * 19) * 23 = 223092870
  rw [nth_prime_two]
  change (((((((prod_primes 1 * Nat.nth Nat.Prime 1) * 5) * 7) * 11) * 13) * 17) * 19) * 23 = 223092870
  rw [nth_prime_one]
  change ((((((((prod_primes 0 * Nat.nth Nat.Prime 0) * 3) * 5) * 7) * 11) * 13) * 17) * 19) * 23 = 223092870
  rw [nth_prime_zero]
  rfl

theorem a_nine_eq : a 9 = 49770428644836901 := by
  dsimp [a]
  rw [prod_primes_eq, prod_primes_nine_eq]
  rfl

theorem divisible_by_29_sq : 49770428644836901 = 29 ^ 2 * 59180057841661 := by
  rfl

theorem not_squarefree_a_nine : ¬ Squarefree (a 9) := by
  intro h
  have hdvd : 29 ^ 2 ∣ a 9 := by
    use 59180057841661
    rw [a_nine_eq, divisible_by_29_sq]
  have hunit := h 29 hdvd
  rw [Nat.isUnit_iff] at hunit
  revert hunit
  decide

/--
oeis_189409_conjecture_0:
It is conjectured that numbers in this sequence are always squarefree,
and that there are infinitely many primes in this sequence.
-/
theorem oeis_a189409_conjectures.disproof :
  ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  intro h
  exact not_squarefree_a_nine (h.left 9)

