import FormalConjectures.Util.ProblemImports
import Mathlib.Tactic.Ring

open Polynomial

theorem poly_id {R : Type*} [CommRing R] (w : R) (hw : w^12 + w^11 + w^10 + w^9 + w^8 + w^7 + w^6 + w^5 + w^4 + w^3 + w^2 + w + 1 = 0)
  (hw13 : w^13 = 1) :
  let y k := w^k + w^(13 - k) + 2
  (X - C (y 1)) * (X - C (y 2)) * (X - C (y 3)) * (X - C (y 4)) * (X - C (y 5)) * (X - C (y 6)) =
  X^6 - C 21 * X^5 + C 70 * X^4 - C 84 * X^3 + C 45 * X^2 - C 11 * X + C 1 := by
  sorry
