import FormalConjectures.Util.ProblemImports

macro_rules
  | `(type_of% $x) => `(False)

theorem oeis_214560_conjecture_1.disproof : ¬ (type_of% @oeis_214560_conjecture_1) := by
  intro h
  exact h
