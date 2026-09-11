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

theorem oeis_a189409_conjectures.disproof : ¬ (type_of% @oeis_a189409_conjectures) := by
  have h13 : Nat.nth Nat.Prime 5 = 13 := by
    have hc : Nat.count Nat.Prime 13 = 5 := by decide
    simpa only [hc] using Nat.nth_count (by norm_num : Nat.Prime 13)
  have h17 : Nat.nth Nat.Prime 6 = 17 := by
    have hc : Nat.count Nat.Prime 17 = 6 := by decide
    simpa only [hc] using Nat.nth_count (by norm_num : Nat.Prime 17)
  have h19 : Nat.nth Nat.Prime 7 = 19 := by
    have hc : Nat.count Nat.Prime 19 = 7 := by decide
    simpa only [hc] using Nat.nth_count (by norm_num : Nat.Prime 19)
  have h23 : Nat.nth Nat.Prime 8 = 23 := by
    have hc : Nat.count Nat.Prime 23 = 8 := by decide
    simpa only [hc] using Nat.nth_count (by norm_num : Nat.Prime 23)
  have ha : a 9 = 49770428644836901 := by
    norm_num [a, Finset.prod_range_succ, h13, h17, h19, h23]
  intro h
  have hs := (Nat.squarefree_iff_prime_squarefree.mp (h.1 9)) 29
    (by norm_num : Nat.Prime 29)
  apply hs
  rw [ha]
  exact ⟨59180057841661, by norm_num⟩
