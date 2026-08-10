import FormalConjectures.Util.ProblemImports
open Nat Finset

def A335624 (n : ℕ) : ℕ :=
  let B : ℕ := Nat.sqrt n + 1
  let R := range B
  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n
      ∧ (let m := x + 3 * y + 4 * z; Nat.sqrt m ^ 2 = m)
    then 1 else 0

theorem test_8 : A335624 8 = 0 := by decide
