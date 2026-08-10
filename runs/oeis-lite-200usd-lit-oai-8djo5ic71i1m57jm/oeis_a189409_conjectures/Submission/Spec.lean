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
private lemma nth_prime_five_eq_thirteen : Nat.nth Nat.Prime 5 = 13 := by
  rw [← show Nat.count Nat.Prime 13 = 5 by decide]
  exact Nat.nth_count (by norm_num [Nat.prime_def_lt] : Nat.Prime 13)

private lemma nth_prime_six_eq_seventeen : Nat.nth Nat.Prime 6 = 17 := by
  rw [← show Nat.count Nat.Prime 17 = 6 by decide]
  exact Nat.nth_count (by norm_num [Nat.prime_def_lt] : Nat.Prime 17)

private lemma nth_prime_seven_eq_nineteen : Nat.nth Nat.Prime 7 = 19 := by
  rw [← show Nat.count Nat.Prime 19 = 7 by decide]
  exact Nat.nth_count (by norm_num [Nat.prime_def_lt] : Nat.Prime 19)

private lemma nth_prime_eight_eq_twentythree : Nat.nth Nat.Prime 8 = 23 := by
  rw [← show Nat.count Nat.Prime 23 = 8 by decide]
  exact Nat.nth_count (by norm_num [Nat.prime_def_lt] : Nat.Prime 23)

theorem oeis_a189409_conjectures.disproof :
  ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  intro h
  have h_not_squarefree : ¬ Squarefree (a 9) := by
    rw [squarefree_iff_prime_squarefree]
    push_neg
    refine ⟨29, by norm_num [Nat.prime_def_lt], ?_⟩
    norm_num [a, Finset.prod_range_succ,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
      Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
      Nat.nth_prime_four_eq_eleven, nth_prime_five_eq_thirteen,
      nth_prime_six_eq_seventeen, nth_prime_seven_eq_nineteen,
      nth_prime_eight_eq_twentythree]
  exact h_not_squarefree (h.1 9)
