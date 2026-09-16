import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

noncomputable def A304522 (n : ℕ) : ℕ :=
  let max_idx := Nat.greatestFib n
  let index_set := Finset.range (max_idx + 1)
  (Finset.image Nat.fib (Finset.filter (fun k =>
    let f := Nat.fib k
    let s := n - f
    f < n ∧ s % 2 = 1 ∧ Squarefree s
  ) index_set)).card

theorem oeis_304522_conjecture_0 :
  (∀ (n : ℕ), 0 < n → A304522 n > 0) ∧
  (∀ (n : ℕ), A304522 n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 27 ∨ n = 83 ∨ n = 31509) := by
  sorry

theorem oeis_304522_conjecture_0.disproof : ¬ (type_of% @oeis_304522_conjecture_0) := by sorry
