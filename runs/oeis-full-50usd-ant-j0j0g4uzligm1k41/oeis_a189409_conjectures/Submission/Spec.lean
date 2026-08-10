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
Helper: if `p` is prime and there are exactly `k` primes below `p`, then the `k`-th prime is `p`.
-/
private lemma nthPrime (k p : ℕ) (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = k) :
    Nat.nth Nat.Prime k = p := by
  rw [← hc]; exact Nat.nth_count hp

private lemma nth0 : Nat.nth Nat.Prime 0 = 2 := nthPrime 0 2 (by norm_num) (by decide)
private lemma nth1 : Nat.nth Nat.Prime 1 = 3 := nthPrime 1 3 (by norm_num) (by decide)
private lemma nth2 : Nat.nth Nat.Prime 2 = 5 := nthPrime 2 5 (by norm_num) (by decide)
private lemma nth3 : Nat.nth Nat.Prime 3 = 7 := nthPrime 3 7 (by norm_num) (by decide)
private lemma nth4 : Nat.nth Nat.Prime 4 = 11 := nthPrime 4 11 (by norm_num) (by decide)
private lemma nth5 : Nat.nth Nat.Prime 5 = 13 := nthPrime 5 13 (by norm_num) (by decide)
private lemma nth6 : Nat.nth Nat.Prime 6 = 17 := nthPrime 6 17 (by norm_num) (by decide)
private lemma nth7 : Nat.nth Nat.Prime 7 = 19 := nthPrime 7 19 (by norm_num) (by decide)
private lemma nth8 : Nat.nth Nat.Prime 8 = 23 := nthPrime 8 23 (by norm_num) (by decide)

/--
The 9th term (n = 9) equals `(2·3·5·7·11·13·17·19·23)^2 + 1 = 223092870^2 + 1 = 49770428644836901`.
-/
private lemma aval : a 9 = 49770428644836901 := by
  unfold a
  rw [show (9:ℕ) = 8+1 from rfl, Finset.prod_range_succ, nth8,
      show (8:ℕ) = 7+1 from rfl, Finset.prod_range_succ, nth7,
      show (7:ℕ) = 6+1 from rfl, Finset.prod_range_succ, nth6,
      show (6:ℕ) = 5+1 from rfl, Finset.prod_range_succ, nth5,
      show (5:ℕ) = 4+1 from rfl, Finset.prod_range_succ, nth4,
      show (4:ℕ) = 3+1 from rfl, Finset.prod_range_succ, nth3,
      show (3:ℕ) = 2+1 from rfl, Finset.prod_range_succ, nth2,
      show (2:ℕ) = 1+1 from rfl, Finset.prod_range_succ, nth1,
      show (1:ℕ) = 0+1 from rfl, Finset.prod_range_succ, nth0,
      Finset.prod_range_zero]
  norm_num

/--
oeis_189409_conjecture_0 is FALSE.

The conjecture claims every term of the sequence is squarefree.  However, the term at `n = 9`
is `a(9) = 49770428644836901 = 29^2 · 53 · 1116604864937`, which is divisible by `29^2` and hence
NOT squarefree.  This refutes the first conjunct, so the whole conjunction is false.
-/
theorem oeis_a189409_conjectures.disproof :
    ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  rintro ⟨hsq, _⟩
  have h9 := hsq 9
  rw [aval] at h9
  have hd : (29:ℕ) * 29 ∣ 49770428644836901 := ⟨59180057841661, by norm_num⟩
  have hu := h9 29 hd
  rw [Nat.isUnit_iff] at hu
  norm_num at hu
