import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

/-
oeis_189409_conjecture_0:
It is conjectured that numbers in this sequence are always squarefree,
and that there are infinitely many primes in this sequence.

This conjecture is **false**: the squarefreeness claim fails already at `n = 9`.
Indeed `a 9 = (2·3·5·7·11·13·17·19·23)^2 + 1 = 223092870^2 + 1 = 49770428644836901`,
and `49770428644836901 = 29^2 · 53 · 1116604864937`, so `29^2 ∣ a 9`.
Hence `a 9` is not squarefree, which refutes the conjunction.
-/

/-- Auxiliary lemma: the `k`-th prime (via `Nat.nth`) equals `n` whenever `n` is prime
and there are exactly `k` primes below `n`. -/
theorem nth_prime_of_count (k n : ℕ) (hp : Nat.Prime n)
    (hc : Nat.count Nat.Prime n = k) : Nat.nth Nat.Prime k = n := by
  have := Nat.nth_count (p := Nat.Prime) (n := n) hp
  rwa [hc] at this

theorem oeis_a189409_conjectures.disproof :
    ¬((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  rintro ⟨hsq, -⟩
  have key : a 9 = 49770428644836901 := by
    have h0 : Nat.nth Nat.Prime 0 = 2 := nth_prime_of_count 0 2 (by norm_num) (by decide)
    have h1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_of_count 1 3 (by norm_num) (by decide)
    have h2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_of_count 2 5 (by norm_num) (by decide)
    have h3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_of_count 3 7 (by norm_num) (by decide)
    have h4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_of_count 4 11 (by norm_num) (by decide)
    have h5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_of_count 5 13 (by norm_num) (by decide)
    have h6 : Nat.nth Nat.Prime 6 = 17 := nth_prime_of_count 6 17 (by norm_num) (by decide)
    have h7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_of_count 7 19 (by norm_num) (by decide)
    have h8 : Nat.nth Nat.Prime 8 = 23 := nth_prime_of_count 8 23 (by norm_num) (by decide)
    unfold a
    simp only [Finset.prod_range_succ, Finset.prod_range_zero,
      h0, h1, h2, h3, h4, h5, h6, h7, h8]
    norm_num
  have h := hsq 9
  rw [key] at h
  have hdvd : 29 * 29 ∣ 49770428644836901 := ⟨59180057841661, by norm_num⟩
  have := h 29 hdvd
  rw [Nat.isUnit_iff] at this
  norm_num at this
