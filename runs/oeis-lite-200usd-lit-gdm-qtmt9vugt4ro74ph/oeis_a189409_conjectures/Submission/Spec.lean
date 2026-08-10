import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

theorem prod_range_nine (f : ℕ → ℕ) :
  (range 9).prod f = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 := by
  change ∏ x ∈ range (8 + 1), f x = _
  rw [prod_range_succ]
  change (∏ x ∈ range (7 + 1), f x) * f 8 = _
  rw [prod_range_succ]
  change (∏ x ∈ range (6 + 1), f x) * f 7 * f 8 = _
  rw [prod_range_succ]
  change (∏ x ∈ range (5 + 1), f x) * f 6 * f 7 * f 8 = _
  rw [prod_range_succ]
  change (∏ x ∈ range (4 + 1), f x) * f 5 * f 6 * f 7 * f 8 = _
  rw [prod_range_succ]
  change (∏ x ∈ range (3 + 1), f x) * f 4 * f 5 * f 6 * f 7 * f 8 = _
  rw [prod_range_succ]
  change (∏ x ∈ range (2 + 1), f x) * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 = _
  rw [prod_range_succ]
  change (∏ x ∈ range (1 + 1), f x) * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 = _
  rw [prod_range_succ]
  change (∏ x ∈ range (0 + 1), f x) * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 = _
  rw [prod_range_succ]
  rw [prod_range_zero]
  ring

theorem nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have count_13 : Nat.count Nat.Prime 13 = 5 := rfl
  have prime_13 : Nat.Prime 13 := by decide
  have nth_count_13 := Nat.nth_count prime_13
  rw [count_13] at nth_count_13
  exact nth_count_13

theorem nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have count_17 : Nat.count Nat.Prime 17 = 6 := rfl
  have prime_17 : Nat.Prime 17 := by decide
  have nth_count_17 := Nat.nth_count prime_17
  rw [count_17] at nth_count_17
  exact nth_count_17

theorem nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have count_19 : Nat.count Nat.Prime 19 = 7 := rfl
  have prime_19 : Nat.Prime 19 := by decide
  have nth_count_19 := Nat.nth_count prime_19
  rw [count_19] at nth_count_19
  exact nth_count_19

theorem nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have count_23 : Nat.count Nat.Prime 23 = 8 := rfl
  have prime_23 : Nat.Prime 23 := by decide
  have nth_count_23 := Nat.nth_count prime_23
  rw [count_23] at nth_count_23
  exact nth_count_23

theorem a_nine : a 9 = 49770428644836901 := by
  unfold a
  rw [prod_range_nine]
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five,
      nth_prime_three_eq_seven, nth_prime_four_eq_eleven,
      nth_prime_five, nth_prime_six, nth_prime_seven, nth_prime_eight]
  rfl

theorem not_squarefree_a_nine : ¬ Squarefree (a 9) := by
  intro h
  have hdiv : 29 * 29 ∣ a 9 := by
    rw [a_nine]
    use 59180057841661
  have h2 := h 29 hdiv
  rw [isUnit_iff_eq_one] at h2
  contradiction

/--
oeis_189409_conjecture_0:
It is conjectured that numbers in this sequence are always squarefree,
and that there are infinitely many primes in this sequence.
-/
theorem oeis_a189409_conjectures.disproof :
  ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  intro h
  have h_sqfree := h.left 9
  exact not_squarefree_a_nine h_sqfree

