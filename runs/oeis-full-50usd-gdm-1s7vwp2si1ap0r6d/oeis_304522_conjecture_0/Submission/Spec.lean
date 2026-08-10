import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

/--
A304522: Number of ordered ways to write $n$ as the sum of a Fibonacci number and a positive odd squarefree number.
The count is over the number of distinct Fibonacci values $f$ such that $n - f$ is a positive odd squarefree number.
$$a(n) = \left| \left\{ F \in \{F_k\}_{k=0}^\infty ~\middle|~ F < n \land \text{Odd}(n - F) \land \text{Squarefree}(n - F) \right\} \right|$$
-/
noncomputable def A304522 (n : ℕ) : ℕ :=
  let max_idx := Nat.greatestFib n
  let index_set := Finset.range (max_idx + 1)
  (Finset.image Nat.fib (Finset.filter (fun k =>
    let f := Nat.fib k
    let s := n - f
    f < n ∧
    s % 2 = 1 ∧
    Squarefree s
  ) index_set)).card

/--
oeis_304522_conjecture_0: Conjecture: a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 27, 83, 31509.
-/
theorem oeis_304522_conjecture_0 :
  (∀ (n : ℕ), 0 < n → A304522 n > 0) ∧
  (∀ (n : ℕ), A304522 n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 27 ∨ n = 83 ∨ n = 31509) := by
  sorry
