import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let max_x : ℕ := (n - 1) / 2
  (Icc 1 max_x).sum fun x =>
    let y : ℕ := n - x
    if Nat.Prime (6 * x - 1) ∧
       Nat.Prime (6 * x + 1) ∧
       Nat.Prime (6 * y - 1) ∧
       Nat.Prime (6 * y + 1)
    then 1 else 0

set_option google.answer "postpone"

theorem oeis_187759_conjecture_0 (n : ℕ) :
    (n > 200 ∧ n ∉ ({211, 226, 541, 701} : Finset ℕ)) → a n > 0 := by
  exact answer(sorry)

theorem oeis_187759_conjecture_0.disproof : ¬ (type_of% @oeis_187759_conjecture_0) := sorry
