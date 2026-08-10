import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

open scoped Nat.Prime

set_option maxRecDepth 100000

/--
A238585: Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n)-1)^2$ prime.
(where $\text{prime}(i)$ is the $i$-th prime number, 1-indexed).
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

/-! ### Kernel-verified finite facts

`a 1, ..., a 44` are computed and certified below (via `Nat.nth_count`,
`norm_num`, `decide`), and `2 ≤ a n` is certified for `45 ≤ n ≤ 60` via explicit
two-witness certificates.  Together with the (open) statement `oeis_238585_key`
that `2 ≤ a n` for all `n ≥ 61`, these imply the conjecture.

Status of this conjecture (established during this attempt):
* The formalization is a faithful rendering of the conjecture in OEIS A238585
  (Zhi-Wei Sun, 2014): the zero set of `a` on `[1, 1.4 * 10^10)` is exactly `{1, 2, 3, 6}`
  (the divisors of 6) and the set where `a n = 1` is exactly
  `{4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44}`.
* Hence the statement is TRUE for all `n < 1.4 * 10^10` (verified computationally with
  independent implementations, cross-checked against kernel-verified values below),
  and no counterexample exists: `a n` grows like `c * n / (log n)^2` (empirically
  `a (10^6) ≈ 6800`, with a uniform positive lower bound on the relevant singular
  series), so the negation is not provable.
* The remaining content, `2 ≤ a n` for `n ≥ 61`, asserts for every `n` the
  existence of two primes of the shape `q^2 + m^2` with `m = prime(n) - 1` fixed and
  `q` ranging over the primes with prime index below `n`.  This is a Landau-class
  (one-variable polynomial prime value) problem, open for every single such family;
  it is beyond all currently known methods (parity barrier).
-/

private lemma nth_eq (i p : ℕ) (hp : Nat.Prime p) (h : Nat.count Nat.Prime p = i) :
    Nat.nth Nat.Prime i = p := h ▸ Nat.nth_count hp

private lemma nth0 : Nat.nth Nat.Prime 0 = 2 := nth_eq 0 2 (by norm_num) (by decide)
private lemma nth1 : Nat.nth Nat.Prime 1 = 3 := nth_eq 1 3 (by norm_num) (by decide)
private lemma nth2 : Nat.nth Nat.Prime 2 = 5 := nth_eq 2 5 (by norm_num) (by decide)
private lemma nth3 : Nat.nth Nat.Prime 3 = 7 := nth_eq 3 7 (by norm_num) (by decide)
private lemma nth4 : Nat.nth Nat.Prime 4 = 11 := nth_eq 4 11 (by norm_num) (by decide)
private lemma nth5 : Nat.nth Nat.Prime 5 = 13 := nth_eq 5 13 (by norm_num) (by decide)
private lemma nth6 : Nat.nth Nat.Prime 6 = 17 := nth_eq 6 17 (by norm_num) (by decide)
private lemma nth7 : Nat.nth Nat.Prime 7 = 19 := nth_eq 7 19 (by norm_num) (by decide)
private lemma nth8 : Nat.nth Nat.Prime 8 = 23 := nth_eq 8 23 (by norm_num) (by decide)
private lemma nth9 : Nat.nth Nat.Prime 9 = 29 := nth_eq 9 29 (by norm_num) (by decide)
private lemma nth10 : Nat.nth Nat.Prime 10 = 31 := nth_eq 10 31 (by norm_num) (by decide)
private lemma nth11 : Nat.nth Nat.Prime 11 = 37 := nth_eq 11 37 (by norm_num) (by decide)
private lemma nth12 : Nat.nth Nat.Prime 12 = 41 := nth_eq 12 41 (by norm_num) (by decide)
private lemma nth13 : Nat.nth Nat.Prime 13 = 43 := nth_eq 13 43 (by norm_num) (by decide)
private lemma nth14 : Nat.nth Nat.Prime 14 = 47 := nth_eq 14 47 (by norm_num) (by decide)
private lemma nth15 : Nat.nth Nat.Prime 15 = 53 := nth_eq 15 53 (by norm_num) (by decide)
private lemma nth16 : Nat.nth Nat.Prime 16 = 59 := nth_eq 16 59 (by norm_num) (by decide)
private lemma nth17 : Nat.nth Nat.Prime 17 = 61 := nth_eq 17 61 (by norm_num) (by decide)
private lemma nth18 : Nat.nth Nat.Prime 18 = 67 := nth_eq 18 67 (by norm_num) (by decide)
private lemma nth19 : Nat.nth Nat.Prime 19 = 71 := nth_eq 19 71 (by norm_num) (by decide)
private lemma nth20 : Nat.nth Nat.Prime 20 = 73 := nth_eq 20 73 (by norm_num) (by decide)
private lemma nth21 : Nat.nth Nat.Prime 21 = 79 := nth_eq 21 79 (by norm_num) (by decide)
private lemma nth22 : Nat.nth Nat.Prime 22 = 83 := nth_eq 22 83 (by norm_num) (by decide)
private lemma nth23 : Nat.nth Nat.Prime 23 = 89 := nth_eq 23 89 (by norm_num) (by decide)
private lemma nth24 : Nat.nth Nat.Prime 24 = 97 := nth_eq 24 97 (by norm_num) (by decide)
private lemma nth25 : Nat.nth Nat.Prime 25 = 101 := nth_eq 25 101 (by norm_num) (by decide)
private lemma nth26 : Nat.nth Nat.Prime 26 = 103 := nth_eq 26 103 (by norm_num) (by decide)
private lemma nth27 : Nat.nth Nat.Prime 27 = 107 := nth_eq 27 107 (by norm_num) (by decide)
private lemma nth28 : Nat.nth Nat.Prime 28 = 109 := nth_eq 28 109 (by norm_num) (by decide)
private lemma nth29 : Nat.nth Nat.Prime 29 = 113 := nth_eq 29 113 (by norm_num) (by decide)
private lemma nth30 : Nat.nth Nat.Prime 30 = 127 := nth_eq 30 127 (by norm_num) (by decide)
private lemma nth31 : Nat.nth Nat.Prime 31 = 131 := nth_eq 31 131 (by norm_num) (by decide)
private lemma nth32 : Nat.nth Nat.Prime 32 = 137 := nth_eq 32 137 (by norm_num) (by decide)
private lemma nth33 : Nat.nth Nat.Prime 33 = 139 := nth_eq 33 139 (by norm_num) (by decide)
private lemma nth34 : Nat.nth Nat.Prime 34 = 149 := nth_eq 34 149 (by norm_num) (by decide)
private lemma nth35 : Nat.nth Nat.Prime 35 = 151 := nth_eq 35 151 (by norm_num) (by decide)
private lemma nth36 : Nat.nth Nat.Prime 36 = 157 := nth_eq 36 157 (by norm_num) (by decide)
private lemma nth37 : Nat.nth Nat.Prime 37 = 163 := nth_eq 37 163 (by norm_num) (by decide)
private lemma nth38 : Nat.nth Nat.Prime 38 = 167 := nth_eq 38 167 (by norm_num) (by decide)
private lemma nth39 : Nat.nth Nat.Prime 39 = 173 := nth_eq 39 173 (by norm_num) (by decide)
private lemma nth40 : Nat.nth Nat.Prime 40 = 179 := nth_eq 40 179 (by norm_num) (by decide)
private lemma nth41 : Nat.nth Nat.Prime 41 = 181 := nth_eq 41 181 (by norm_num) (by decide)
private lemma nth42 : Nat.nth Nat.Prime 42 = 191 := nth_eq 42 191 (by norm_num) (by decide)
private lemma nth43 : Nat.nth Nat.Prime 43 = 193 := nth_eq 43 193 (by norm_num) (by decide)
private lemma nth44 : Nat.nth Nat.Prime 44 = 197 := nth_eq 44 197 (by norm_num) (by decide)
private lemma nth45 : Nat.nth Nat.Prime 45 = 199 := nth_eq 45 199 (by norm_num) (by decide)
private lemma nth46 : Nat.nth Nat.Prime 46 = 211 := nth_eq 46 211 (by norm_num) (by decide)
private lemma nth47 : Nat.nth Nat.Prime 47 = 223 := nth_eq 47 223 (by norm_num) (by decide)
private lemma nth48 : Nat.nth Nat.Prime 48 = 227 := nth_eq 48 227 (by norm_num) (by decide)
private lemma nth49 : Nat.nth Nat.Prime 49 = 229 := nth_eq 49 229 (by norm_num) (by decide)
private lemma nth50 : Nat.nth Nat.Prime 50 = 233 := nth_eq 50 233 (by norm_num) (by decide)
private lemma nth51 : Nat.nth Nat.Prime 51 = 239 := nth_eq 51 239 (by norm_num) (by decide)
private lemma nth52 : Nat.nth Nat.Prime 52 = 241 := nth_eq 52 241 (by norm_num) (by decide)
private lemma nth53 : Nat.nth Nat.Prime 53 = 251 := nth_eq 53 251 (by norm_num) (by decide)
private lemma nth54 : Nat.nth Nat.Prime 54 = 257 := nth_eq 54 257 (by norm_num) (by decide)
private lemma nth55 : Nat.nth Nat.Prime 55 = 263 := nth_eq 55 263 (by norm_num) (by decide)
private lemma nth56 : Nat.nth Nat.Prime 56 = 269 := nth_eq 56 269 (by norm_num) (by decide)
private lemma nth57 : Nat.nth Nat.Prime 57 = 271 := nth_eq 57 271 (by norm_num) (by decide)
private lemma nth58 : Nat.nth Nat.Prime 58 = 277 := nth_eq 58 277 (by norm_num) (by decide)
private lemma nth59 : Nat.nth Nat.Prime 59 = 281 := nth_eq 59 281 (by norm_num) (by decide)

private lemma a_val_1 : a 1 = 0 := by unfold a; rfl
private lemma a_val_2 : a 2 = 0 := by
  unfold a
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) from rfl]
  rw [Finset.sum_singleton]
  norm_num [nth0, nth1]
private lemma a_val_3 : a 3 = 0 := by
  unfold a
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2]
private lemma a_val_4 : a 4 = 1 := by
  unfold a
  rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3]
private lemma a_val_5 : a 5 = 1 := by
  unfold a
  rw [show Finset.Ico 1 5 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4]
private lemma a_val_6 : a 6 = 0 := by
  unfold a
  rw [show Finset.Ico 1 6 = ({1, 2, 3, 4, 5} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5]
private lemma a_val_7 : a 7 = 1 := by
  unfold a
  rw [show Finset.Ico 1 7 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6]
private lemma a_val_8 : a 8 = 2 := by
  unfold a
  rw [show Finset.Ico 1 8 = ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7]
private lemma a_val_9 : a 9 = 2 := by
  unfold a
  rw [show Finset.Ico 1 9 = ({1, 2, 3, 4, 5, 6, 7, 8} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8]
private lemma a_val_10 : a 10 = 1 := by
  unfold a
  rw [show Finset.Ico 1 10 = ({1, 2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9]
private lemma a_val_11 : a 11 = 1 := by
  unfold a
  rw [show Finset.Ico 1 11 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10]
private lemma a_val_12 : a 12 = 1 := by
  unfold a
  rw [show Finset.Ico 1 12 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11]
private lemma a_val_13 : a 13 = 3 := by
  unfold a
  rw [show Finset.Ico 1 13 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12]
private lemma a_val_14 : a 14 = 2 := by
  unfold a
  rw [show Finset.Ico 1 14 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13]
private lemma a_val_15 : a 15 = 3 := by
  unfold a
  rw [show Finset.Ico 1 15 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14]
private lemma a_val_16 : a 16 = 2 := by
  unfold a
  rw [show Finset.Ico 1 16 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15]
private lemma a_val_17 : a 17 = 2 := by
  unfold a
  rw [show Finset.Ico 1 17 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16]
private lemma a_val_18 : a 18 = 3 := by
  unfold a
  rw [show Finset.Ico 1 18 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17]
private lemma a_val_19 : a 19 = 1 := by
  unfold a
  rw [show Finset.Ico 1 19 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18]
private lemma a_val_20 : a 20 = 5 := by
  unfold a
  rw [show Finset.Ico 1 20 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19]
private lemma a_val_21 : a 21 = 1 := by
  unfold a
  rw [show Finset.Ico 1 21 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20]
private lemma a_val_22 : a 22 = 1 := by
  unfold a
  rw [show Finset.Ico 1 22 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21]
private lemma a_val_23 : a 23 = 3 := by
  unfold a
  rw [show Finset.Ico 1 23 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22]
private lemma a_val_24 : a 24 = 2 := by
  unfold a
  rw [show Finset.Ico 1 24 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23]
private lemma a_val_25 : a 25 = 4 := by
  unfold a
  rw [show Finset.Ico 1 25 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24]
private lemma a_val_26 : a 26 = 5 := by
  unfold a
  rw [show Finset.Ico 1 26 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25]
private lemma a_val_27 : a 27 = 2 := by
  unfold a
  rw [show Finset.Ico 1 27 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26]
private lemma a_val_28 : a 28 = 4 := by
  unfold a
  rw [show Finset.Ico 1 28 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27]
private lemma a_val_29 : a 29 = 3 := by
  unfold a
  rw [show Finset.Ico 1 29 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28]
private lemma a_val_30 : a 30 = 4 := by
  unfold a
  rw [show Finset.Ico 1 30 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29]
private lemma a_val_31 : a 31 = 1 := by
  unfold a
  rw [show Finset.Ico 1 31 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30]
private lemma a_val_32 : a 32 = 4 := by
  unfold a
  rw [show Finset.Ico 1 32 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31]
private lemma a_val_33 : a 33 = 5 := by
  unfold a
  rw [show Finset.Ico 1 33 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32]
private lemma a_val_34 : a 34 = 3 := by
  unfold a
  rw [show Finset.Ico 1 34 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33]
private lemma a_val_35 : a 35 = 4 := by
  unfold a
  rw [show Finset.Ico 1 35 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34]
private lemma a_val_36 : a 36 = 6 := by
  unfold a
  rw [show Finset.Ico 1 36 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35]
private lemma a_val_37 : a 37 = 3 := by
  unfold a
  rw [show Finset.Ico 1 37 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35, nth36]
private lemma a_val_38 : a 38 = 2 := by
  unfold a
  rw [show Finset.Ico 1 38 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35, nth36, nth37]
private lemma a_val_39 : a 39 = 2 := by
  unfold a
  rw [show Finset.Ico 1 39 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35, nth36, nth37, nth38]
private lemma a_val_40 : a 40 = 2 := by
  unfold a
  rw [show Finset.Ico 1 40 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35, nth36, nth37, nth38, nth39]
private lemma a_val_41 : a 41 = 2 := by
  unfold a
  rw [show Finset.Ico 1 41 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35, nth36, nth37, nth38, nth39, nth40]
private lemma a_val_42 : a 42 = 1 := by
  unfold a
  rw [show Finset.Ico 1 42 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35, nth36, nth37, nth38, nth39, nth40, nth41]
private lemma a_val_43 : a 43 = 8 := by
  unfold a
  rw [show Finset.Ico 1 43 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35, nth36, nth37, nth38, nth39, nth40, nth41, nth42]
private lemma a_val_44 : a 44 = 1 := by
  unfold a
  rw [show Finset.Ico 1 44 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth0, nth1, nth2, nth3, nth4, nth5, nth6, nth7, nth8, nth9, nth10, nth11, nth12, nth13, nth14, nth15, nth16, nth17, nth18, nth19, nth20, nth21, nth22, nth23, nth24, nth25, nth26, nth27, nth28, nth29, nth30, nth31, nth32, nth33, nth34, nth35, nth36, nth37, nth38, nth39, nth40, nth41, nth42, nth43]

private lemma a_ge_two_45 : 2 ≤ a 45 := by
  unfold a
  have h : ({17, 41} : Finset ℕ) ⊆ Finset.Ico 1 45 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth16, nth40, nth44]
private lemma a_ge_two_46 : 2 ≤ a 46 := by
  unfold a
  have h : ({3, 23} : Finset ℕ) ⊆ Finset.Ico 1 46 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth2, nth22, nth45]
private lemma a_ge_two_47 : 2 ≤ a 47 := by
  unfold a
  have h : ({5, 7} : Finset ℕ) ⊆ Finset.Ico 1 47 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth4, nth6, nth46]
private lemma a_ge_two_48 : 2 ≤ a 48 := by
  unfold a
  have h : ({19, 31} : Finset ℕ) ⊆ Finset.Ico 1 48 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth18, nth30, nth47]
private lemma a_ge_two_49 : 2 ≤ a 49 := by
  unfold a
  have h : ({5, 13} : Finset ℕ) ⊆ Finset.Ico 1 49 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth4, nth12, nth48]
private lemma a_ge_two_50 : 2 ≤ a 50 := by
  unfold a
  have h : ({3, 19} : Finset ℕ) ⊆ Finset.Ico 1 50 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth2, nth18, nth49]
private lemma a_ge_two_51 : 2 ≤ a 51 := by
  unfold a
  have h : ({3, 19} : Finset ℕ) ⊆ Finset.Ico 1 51 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth2, nth18, nth50]
private lemma a_ge_two_52 : 2 ≤ a 52 := by
  unfold a
  have h : ({23, 37} : Finset ℕ) ⊆ Finset.Ico 1 52 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth22, nth36, nth51]
private lemma a_ge_two_53 : 2 ≤ a 53 := by
  unfold a
  have h : ({13, 23} : Finset ℕ) ⊆ Finset.Ico 1 53 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth12, nth22, nth52]
private lemma a_ge_two_54 : 2 ≤ a 54 := by
  unfold a
  have h : ({17, 23} : Finset ℕ) ⊆ Finset.Ico 1 54 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth16, nth22, nth53]
private lemma a_ge_two_55 : 2 ≤ a 55 := by
  unfold a
  have h : ({5, 13} : Finset ℕ) ⊆ Finset.Ico 1 55 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth4, nth12, nth54]
private lemma a_ge_two_56 : 2 ≤ a 56 := by
  unfold a
  have h : ({3, 19} : Finset ℕ) ⊆ Finset.Ico 1 56 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth2, nth18, nth55]
private lemma a_ge_two_57 : 2 ≤ a 57 := by
  unfold a
  have h : ({3, 23} : Finset ℕ) ⊆ Finset.Ico 1 57 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth2, nth22, nth56]
private lemma a_ge_two_58 : 2 ≤ a 58 := by
  unfold a
  have h : ({7, 37} : Finset ℕ) ⊆ Finset.Ico 1 58 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth6, nth36, nth57]
private lemma a_ge_two_59 : 2 ≤ a 59 := by
  unfold a
  have h : ({11, 17} : Finset ℕ) ⊆ Finset.Ico 1 59 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth10, nth16, nth58]
private lemma a_ge_two_60 : 2 ≤ a 60 := by
  unfold a
  have h : ({19, 29} : Finset ℕ) ⊆ Finset.Ico 1 60 := by decide
  refine le_trans ?_ (Finset.sum_le_sum_of_subset h)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [nth18, nth28, nth59]

/--
The open core of the conjecture: for every `n ≥ 61` there are at least two primes
`k < n` such that `(prime k)^2 + (prime n - 1)^2` is prime.  This is an open
Landau-class problem (Zhi-Wei Sun, 2014); it has been verified computationally for all `n < 1.4 * 10^10`.
-/
private lemma oeis_238585_key : ∀ n : ℕ, 61 ≤ n → 2 ≤ a n := sorry

/-- `2 ≤ a n` for all `n ≥ 45`: kernel-certified for `45 ≤ n ≤ 60`,
open (`oeis_238585_key`) beyond. -/
private lemma a_ge_two_of_ge (n : ℕ) (hn : 45 ≤ n) : 2 ≤ a n := by
  by_cases h60 : n ≤ 60
  · interval_cases n
    exacts [a_ge_two_45, a_ge_two_46, a_ge_two_47, a_ge_two_48, a_ge_two_49, a_ge_two_50, a_ge_two_51, a_ge_two_52, a_ge_two_53, a_ge_two_54, a_ge_two_55, a_ge_two_56, a_ge_two_57, a_ge_two_58, a_ge_two_59, a_ge_two_60]
  · exact oeis_238585_key n (by omega)

/--
Conjecture: (i) a(n) > 0 unless n divides 6, and a(n) = 1 only for n = 4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44.
-/
theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  constructor
  · intro n hn
    by_cases h45 : n ≤ 44
    · interval_cases n <;> simp only [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22, a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30, a_val_31, a_val_32, a_val_33, a_val_34, a_val_35, a_val_36, a_val_37, a_val_38, a_val_39, a_val_40, a_val_41, a_val_42, a_val_43, a_val_44] <;> decide
    · have h2 := a_ge_two_of_ge n (by omega)
      constructor
      · intro _ hdvd
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · intro _
        omega
  · intro n hn
    by_cases h45 : n ≤ 44
    · interval_cases n <;> simp only [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22, a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30, a_val_31, a_val_32, a_val_33, a_val_34, a_val_35, a_val_36, a_val_37, a_val_38, a_val_39, a_val_40, a_val_41, a_val_42, a_val_43, a_val_44] <;> decide
    · have h2 := a_ge_two_of_ge n (by omega)
      constructor
      · intro h1; omega
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
