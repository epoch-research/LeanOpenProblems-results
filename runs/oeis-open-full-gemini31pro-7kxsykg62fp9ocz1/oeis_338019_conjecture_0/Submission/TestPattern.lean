import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  let M := n.sqrt
  let R := range (M + 1)
  let BoundingBox := (R.product R).product (R.product R)
  Finset.card
    (BoundingBox.filter (fun p =>
      let ((x, y), (z, w)) := p
      x^2 + y^2 + z^2 + w^2 = n ∧
      let c := 3 * x + 10 * y + 36 * z
      c > 0 ∧ c.sqrt * c.sqrt = c
    ))
