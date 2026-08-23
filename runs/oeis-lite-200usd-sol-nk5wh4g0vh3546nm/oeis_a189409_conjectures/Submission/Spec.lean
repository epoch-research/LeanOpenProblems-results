import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

/-- The squarefreeness assertion already fails at `n = 9`, since `29² ∣ a 9`. -/
theorem oeis_a189409_conjectures.disproof :
    ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  have h5 : Nat.nth Nat.Prime 5 = 13 := by
    rw [← show Nat.count Nat.Prime 13 = 5 by decide]
    exact Nat.nth_count (by norm_num)
  have h6 : Nat.nth Nat.Prime 6 = 17 := by
    rw [← show Nat.count Nat.Prime 17 = 6 by decide]
    exact Nat.nth_count (by norm_num)
  have h7 : Nat.nth Nat.Prime 7 = 19 := by
    rw [← show Nat.count Nat.Prime 19 = 7 by decide]
    exact Nat.nth_count (by norm_num)
  have h8 : Nat.nth Nat.Prime 8 = 23 := by
    rw [← show Nat.count Nat.Prime 23 = 8 by decide]
    exact Nat.nth_count (by norm_num)
  rintro ⟨hsquarefree, _⟩
  have h := hsquarefree 9
  rw [Nat.squarefree_iff_prime_squarefree] at h
  apply h 29 (by norm_num)
  norm_num [a, Finset.prod_range_succ, h5, h6, h7, h8]
