import Submission.Spec
import Mathlib

theorem oeis_290472_conjecture_3.disproof : ¬ (type_of% @oeis_290472_conjecture_3) :=
  fun h => by
    have H := h 286 (by decide)
    revert H
    exact decide (a 286 > 1 → False)
