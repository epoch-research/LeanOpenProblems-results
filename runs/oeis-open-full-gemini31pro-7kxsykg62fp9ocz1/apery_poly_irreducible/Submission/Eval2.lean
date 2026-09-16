import Submission.Spec
open Polynomial

theorem apery_poly_2 : apery_poly 2 = C 1 + C 12 * X + C 6 * X^2 := by
  unfold apery_poly
  simp
  -- we can just use `ring` or something?
  sorry
