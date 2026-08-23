import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

private lemma nth_prime_five_eq_thirteen : nth Nat.Prime 5 = 13 :=
  nth_count (by norm_num : Nat.Prime 13)

private lemma nth_prime_six_eq_seventeen : nth Nat.Prime 6 = 17 :=
  nth_count (by norm_num : Nat.Prime 17)

private lemma nth_prime_seven_eq_nineteen : nth Nat.Prime 7 = 19 :=
  nth_count (by norm_num : Nat.Prime 19)

private lemma nth_prime_eight_eq_twenty_three : nth Nat.Prime 8 = 23 :=
  nth_count (by norm_num : Nat.Prime 23)

private lemma primorial_nine :
    (range 9).prod (fun k : ℕ => Nat.nth Nat.Prime k) = 223092870 := by
  simp only [prod_range_succ, prod_range_zero]
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five,
      nth_prime_three_eq_seven, nth_prime_four_eq_eleven,
      nth_prime_five_eq_thirteen, nth_prime_six_eq_seventeen,
      nth_prime_seven_eq_nineteen, nth_prime_eight_eq_twenty_three]
  norm_num

/--
The OEIS A189409 conjectures fail: `a 9 = 29^2 * 53 * 1116604864937` is not squarefree.
-/
theorem oeis_a189409_conjectures.disproof :
    ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  intro h
  have h29 : Nat.Prime 29 := by norm_num
  have hdiv : 29 * 29 ∣ a 9 := by
    unfold a
    rw [primorial_nine]
    exact ⟨59180057841661, by norm_num⟩
  exact squarefree_iff_prime_squarefree.1 (h.1 9) 29 h29 hdiv
