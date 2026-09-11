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
theorem oeis_a189409_conjectures :
  (∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)} :=
by sorry

theorem nth_prime_five_eq : nth Nat.Prime 5 = 13 := by
  have h : Nat.count Nat.Prime 13 = 5 := by decide
  rw [← h]; exact nth_count (by norm_num)

theorem nth_prime_six_eq : nth Nat.Prime 6 = 17 := by
  have h : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← h]; exact nth_count (by norm_num)

theorem nth_prime_seven_eq : nth Nat.Prime 7 = 19 := by
  have h : Nat.count Nat.Prime 19 = 7 := by decide
  rw [← h]; exact nth_count (by norm_num)

theorem nth_prime_eight_eq : nth Nat.Prime 8 = 23 := by
  have h : Nat.count Nat.Prime 23 = 8 := by decide
  rw [← h]; exact nth_count (by norm_num)

/-- `a 9 = (2·3·5·7·11·13·17·19·23)^2 + 1 = 223092870^2 + 1`. -/
theorem a_nine : a 9 = 49770428644836901 := by
  unfold a
  simp only [prod_range_succ, prod_range_zero, nth_prime_zero_eq_two, nth_prime_one_eq_three,
    nth_prime_two_eq_five, nth_prime_three_eq_seven, nth_prime_four_eq_eleven,
    nth_prime_five_eq, nth_prime_six_eq, nth_prime_seven_eq, nth_prime_eight_eq]
  norm_num

/-- The conjecture is false: `a 9 = 49770428644836901 = 29^2 · 53 · 1116604864937`
is not squarefree. -/
theorem oeis_a189409_conjectures.disproof : ¬ (type_of% @oeis_a189409_conjectures) := by
  intro ⟨h, _⟩
  have h9 := h 9
  rw [a_nine] at h9
  have hdvd : (29 : ℕ) * 29 ∣ 49770428644836901 := by norm_num
  have := h9 29 hdvd
  norm_num at this
