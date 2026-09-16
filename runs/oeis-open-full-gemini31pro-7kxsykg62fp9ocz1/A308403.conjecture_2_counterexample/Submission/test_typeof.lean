import Mathlib
import FormalConjectures.Util.ProblemImports

theorem my_false : 1 = 0 := sorry

theorem my_false_disproof : ¬ (type_of% @my_false) := by
  -- type_of% @my_false should be 1 = 0
  exact Nat.one_ne_zero

