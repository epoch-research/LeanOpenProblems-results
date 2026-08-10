import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

theorem nth_prime_five_eq_thirteen : Nat.nth Nat.Prime 5 = 13 := by
  have h : Nat.count Nat.Prime 13 = 5 := by decide
  have := Nat.nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 13)
  rwa [h] at this

theorem nth_prime_six_eq_seventeen : Nat.nth Nat.Prime 6 = 17 := by
  have h : Nat.count Nat.Prime 17 = 6 := by decide
  have := Nat.nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 17)
  rwa [h] at this

theorem nth_prime_seven_eq_nineteen : Nat.nth Nat.Prime 7 = 19 := by
  have h : Nat.count Nat.Prime 19 = 7 := by decide
  have := Nat.nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 19)
  rwa [h] at this

theorem nth_prime_eight_eq_twentythree : Nat.nth Nat.Prime 8 = 23 := by
  have h : Nat.count Nat.Prime 23 = 8 := by decide
  have := Nat.nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 23)
  rwa [h] at this

/-- The value of the ninth term: `(2·3·5·7·11·13·17·19·23)² + 1 = 223092870² + 1`. -/
theorem a_nine_eq : a 9 = 49770428644836901 := by
  unfold a
  rw [show (9 : ℕ) = 8 + 1 from rfl, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
      Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
      Nat.nth_prime_four_eq_eleven, nth_prime_five_eq_thirteen,
      nth_prime_six_eq_seventeen, nth_prime_seven_eq_nineteen,
      nth_prime_eight_eq_twentythree]
  norm_num

/--
Disproof of oeis_189409_conjecture_0: the term `a 9 = 223092870² + 1 = 49770428644836901`
is divisible by `29² = 841` (indeed `49770428644836901 = 29² · 53 · 1116604864937`),
hence not squarefree, refuting the first conjunct.
-/
theorem oeis_a189409_conjectures.disproof :
  ¬((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  rintro ⟨hsq, -⟩
  have h9 := hsq 9
  rw [a_nine_eq] at h9
  have hdvd : (29 : ℕ) * 29 ∣ 49770428644836901 := ⟨59180057841661, by norm_num⟩
  have := h9 29 hdvd
  rw [Nat.isUnit_iff] at this
  exact absurd this (by norm_num)
