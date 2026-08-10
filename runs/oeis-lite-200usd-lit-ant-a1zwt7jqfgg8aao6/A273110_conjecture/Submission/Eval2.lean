import FormalConjectures.Util.ProblemImports
open Nat
def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n
  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2
    if x^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ (IsSquare E)
    then 1 else 0
-- validate specific values against python
#eval (A273110 119, A273110 151, A273110 120, A273110 200, A273110 112)
