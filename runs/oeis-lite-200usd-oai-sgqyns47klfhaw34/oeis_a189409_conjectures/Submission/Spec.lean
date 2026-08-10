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
  intro h
  have hnonsq : ¬ Squarefree (a 9) := by
    rw [Nat.squarefree_iff_prime_squarefree]
    push_neg
    refine ⟨29, ?_, ?_⟩
    · norm_num
    · have h5 : Nat.nth Nat.Prime 5 = 13 := by
        simpa using Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num : Nat.Prime 13)
      have h6 : Nat.nth Nat.Prime 6 = 17 := by
        simpa using Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num : Nat.Prime 17)
      have h7 : Nat.nth Nat.Prime 7 = 19 := by
        simpa using Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num : Nat.Prime 19)
      have h8 : Nat.nth Nat.Prime 8 = 23 := by
        simpa using Nat.nth_count (p := Nat.Prime) (n := 23) (by norm_num : Nat.Prime 23)
      norm_num [a, h5, h6, h7, h8, Finset.prod_range_succ, dvd_iff_mod_eq_zero]
  exact hnonsq (h.1 9)
