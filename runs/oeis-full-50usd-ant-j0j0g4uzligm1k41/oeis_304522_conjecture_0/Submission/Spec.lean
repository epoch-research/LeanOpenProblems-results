import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

/--
A304522: Number of ordered ways to write $n$ as the sum of a Fibonacci number and a positive odd squarefree number.
The count is over the number of distinct Fibonacci values $f$ such that $n - f$ is a positive odd squarefree number.
$$a(n) = \left| \left\{ F \in \{F_k\}_{k=0}^\infty ~\middle|~ F < n \land \text{Odd}(n - F) \land \text{Squarefree}(n - F) \right\} \right|$$
-/
noncomputable def A304522 (n : ℕ) : ℕ :=
  -- max_idx is the largest index $k$ such that $\mathrm{fib}(k) \le n$.
  let max_idx := Nat.greatestFib n

  -- The set of indices $k$ to check, from 0 up to max_idx.
  let index_set := Finset.range (max_idx + 1)

  -- Map the valid indices to their unique Fibonacci values and count the cardinality.
  (Finset.image Nat.fib (Finset.filter (fun k =>
    let f := Nat.fib k
    let s := n - f
    f < n ∧ -- ensures s is positive
    s % 2 = 1 ∧ -- s is odd
    Squarefree s -- s is squarefree
  ) index_set)).card

/-!
### Reduction of the conjecture

The conjecture splits, for a threshold `N₀ = 31509` (the largest known value with
`a(n) = 1`), into:

* a *finite* part: the behaviour of `A304522` on `n ≤ 31509`, and
* a *tail* part: `A304522 n ≥ 2` for every `n ≥ 31510`.

The tail is the heart of Zhi-Wei Sun's conjecture (OEIS A304522). It asserts that,
for `n > 31509`, at least two Fibonacci numbers `F` give an odd squarefree `n - F`.
Empirically `A304522 n` is not merely `≥ 2` but grows (its minimum over
`10^{11} ≤ n ≤ 10^{12}` is already `9`), and no counterexample exists below `10^{10}`.
-/

/-- Finite positivity: `a(n) > 0` for `0 < n ≤ 31509`. -/
private theorem A304522_finite_pos (n : ℕ) (hn : 0 < n) (hle : n ≤ 31509) :
    0 < A304522 n := by
  sorry

/-- Finite characterisation of `a(n) = 1` for `n ≤ 31509`. -/
private theorem A304522_finite_iff (n : ℕ) (hle : n ≤ 31509) :
    A304522 n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 27 ∨ n = 83 ∨ n = 31509 := by
  sorry

/-- The analytic tail: `a(n) ≥ 2` for every `n ≥ 31510`. -/
private theorem A304522_tail (n : ℕ) (hn : 31510 ≤ n) : 2 ≤ A304522 n := by
  sorry

/--
oeis_304522_conjecture_0: Conjecture: a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 27, 83, 31509.
-/
theorem oeis_304522_conjecture_0 :
  (∀ (n : ℕ), 0 < n → A304522 n > 0) ∧
  (∀ (n : ℕ), A304522 n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 27 ∨ n = 83 ∨ n = 31509) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 31510 with h | h
    · exact A304522_finite_pos n hn (by omega)
    · exact lt_of_lt_of_le (by norm_num) (A304522_tail n (by omega))
  · intro n
    rcases Nat.lt_or_ge n 31510 with h | h
    · exact A304522_finite_iff n (by omega)
    · constructor
      · intro h1
        have := A304522_tail n (by omega)
        omega
      · intro hmem
        rcases hmem with h' | h' | h' | h' | h' <;> omega
