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

This conjecture is FALSE: the "always squarefree" claim fails already at `n = 9`.
The product of the first 9 primes is `223092870`, so
`a 9 = 223092870 ^ 2 + 1 = 49770428644836901 = 29 ^ 2 * 53 * 1116604864937`,
which is divisible by `29 ^ 2` and hence not squarefree. This refutes the first
conjunct, and therefore the whole conjunction.
-/
theorem oeis_a189409_conjectures.disproof :
  ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  rintro ⟨h, _⟩
  have n5 : Nat.nth Nat.Prime 5 = 13 := by
    have h : Nat.count Nat.Prime 13 = 5 := by decide
    have := Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num); rwa [h] at this
  have n6 : Nat.nth Nat.Prime 6 = 17 := by
    have h : Nat.count Nat.Prime 17 = 6 := by decide
    have := Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num); rwa [h] at this
  have n7 : Nat.nth Nat.Prime 7 = 19 := by
    have h : Nat.count Nat.Prime 19 = 7 := by decide
    have := Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num); rwa [h] at this
  have n8 : Nat.nth Nat.Prime 8 = 23 := by
    have h : Nat.count Nat.Prime 23 = 8 := by decide
    have := Nat.nth_count (p := Nat.Prime) (n := 23) (by norm_num); rwa [h] at this
  have hval : a 9 = 49770428644836901 := by
    unfold a
    rw [show (9:ℕ) = 8+1 from rfl, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ]
    rw [nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five,
        nth_prime_three_eq_seven, nth_prime_four_eq_eleven, n5, n6, n7, n8]
    norm_num
  have hsf := h 9
  rw [hval] at hsf
  have hdvd : 29 * 29 ∣ 49770428644836901 := by norm_num
  have hu := hsf 29 hdvd
  rw [Nat.isUnit_iff] at hu
  norm_num at hu
