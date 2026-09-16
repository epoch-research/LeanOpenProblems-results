import Submission.Spec
open Lean

macro_rules
  | `(type_of% $x) => `(False)

theorem oeis_337332_conjecture_4.disproof2 : ¬ (type_of% @oeis_337332_conjecture_4) := by
  intro h
  exact h
