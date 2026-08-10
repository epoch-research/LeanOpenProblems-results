import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

/--
oeis_189409_conjecture_0:
It is conjectured that numbers in this sequence are always squarefree,
and that there are infinitely many primes in this sequence.
-/
theorem prime_13 : Nat.Prime 13 := by decide
theorem prime_17 : Nat.Prime 17 := by decide
theorem prime_19 : Nat.Prime 19 := by decide
theorem prime_23 : Nat.Prime 23 := by decide

theorem count_13 : count Nat.Prime 13 = 5 := rfl
theorem count_17 : count Nat.Prime 17 = 6 := rfl
theorem count_19 : count Nat.Prime 19 = 7 := rfl
theorem count_23 : count Nat.Prime 23 = 8 := rfl

theorem nth_5 : nth Nat.Prime 5 = 13 := by
  have := nth_count prime_13
  rw [count_13] at this
  exact this

theorem nth_6 : nth Nat.Prime 6 = 17 := by
  have := nth_count prime_17
  rw [count_17] at this
  exact this

theorem nth_7 : nth Nat.Prime 7 = 19 := by
  have := nth_count prime_19
  rw [count_19] at this
  exact this

theorem nth_8 : nth Nat.Prime 8 = 23 := by
  have := nth_count prime_23
  rw [count_23] at this
  exact this

theorem a_9_val : a 9 = 49770428644836901 := by
  dsimp [a]
  simp only [prod_range_succ, prod_range_zero, one_mul]
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five,
      nth_prime_three_eq_seven, nth_prime_four_eq_eleven, nth_5, nth_6, nth_7, nth_8]
  rfl

theorem not_squarefree_a_9 : ¬ Squarefree (a 9) := by
  intro h
  have hdvd : 29 ^ 2 ∣ a 9 := by
    rw [a_9_val]
    use 59180057841661
    decide
  have hunit := h 29 hdvd
  rw [Nat.isUnit_iff] at hunit
  contradiction

theorem oeis_a189409_conjectures.disproof :
  ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  intro h
  have h_sqfree := h.left
  have h_9_sqfree := h_sqfree 9
  exact not_squarefree_a_9 h_9_sqfree

