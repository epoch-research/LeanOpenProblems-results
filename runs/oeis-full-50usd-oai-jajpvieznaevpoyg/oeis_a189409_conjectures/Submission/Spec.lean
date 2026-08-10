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
  ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) :=
by
  rintro ⟨hsq, _⟩
  have hnot : ¬ Squarefree (a 9) := by
    rw [Nat.squarefree_iff_prime_squarefree]
    push_neg
    refine ⟨29, by norm_num, ?_⟩
    rw [a]
    rw [show (range 9).prod (fun k : ℕ => Nat.nth Nat.Prime k) = 223092870 by
      simp only [Finset.prod_range_succ]
      rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
        Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven,
        show Nat.nth Nat.Prime 5 = 13 by
          have h := Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num : Nat.Prime 13)
          have hc : Nat.count Nat.Prime 13 = 5 := by norm_num [Nat.count_succ]
          rwa [hc] at h,
        show Nat.nth Nat.Prime 6 = 17 by
          have h := Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num : Nat.Prime 17)
          have hc : Nat.count Nat.Prime 17 = 6 := by norm_num [Nat.count_succ]
          rwa [hc] at h,
        show Nat.nth Nat.Prime 7 = 19 by
          have h := Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num : Nat.Prime 19)
          have hc : Nat.count Nat.Prime 19 = 7 := by norm_num [Nat.count_succ]
          rwa [hc] at h,
        show Nat.nth Nat.Prime 8 = 23 by
          have h := Nat.nth_count (p := Nat.Prime) (n := 23) (by norm_num : Nat.Prime 23)
          have hc : Nat.count Nat.Prime 23 = 8 := by norm_num [Nat.count_succ]
          rwa [hc] at h]
      norm_num]
    norm_num
  exact hnot (hsq 9)
