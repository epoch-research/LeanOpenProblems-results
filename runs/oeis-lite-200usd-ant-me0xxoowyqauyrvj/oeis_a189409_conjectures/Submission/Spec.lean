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
theorem oeis_a189409_conjectures.disproof :
    ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  -- The squarefree part of the conjecture already fails: `a 9 = 223092870 ^ 2 + 1`
  -- is divisible by `29 ^ 2 = 841`, hence is not squarefree.
  have n5 : Nat.nth Nat.Prime 5 = 13 := by
    have := Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num)
    rwa [show Nat.count Nat.Prime 13 = 5 from by decide] at this
  have n6 : Nat.nth Nat.Prime 6 = 17 := by
    have := Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num)
    rwa [show Nat.count Nat.Prime 17 = 6 from by decide] at this
  have n7 : Nat.nth Nat.Prime 7 = 19 := by
    have := Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num)
    rwa [show Nat.count Nat.Prime 19 = 7 from by decide] at this
  have n8 : Nat.nth Nat.Prime 8 = 23 := by
    have := Nat.nth_count (p := Nat.Prime) (n := 23) (by norm_num)
    rwa [show Nat.count Nat.Prime 23 = 8 from by decide] at this
  rintro ⟨hsq, -⟩
  have ha : a 9 = 49770428644836901 := by
    simp only [a, Finset.prod_range_succ, Finset.prod_range_zero,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
      Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven, n5, n6, n7, n8]
    norm_num
  have hdvd : (29 : ℕ) * 29 ∣ a 9 := by rw [ha]; norm_num
  have hu := (hsq 9) 29 hdvd
  rw [Nat.isUnit_iff] at hu
  norm_num at hu
