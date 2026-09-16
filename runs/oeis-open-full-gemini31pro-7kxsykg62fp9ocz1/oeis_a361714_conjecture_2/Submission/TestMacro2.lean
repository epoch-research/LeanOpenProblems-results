import FormalConjectures.Util.ProblemImports

theorem test_thm : True := trivial

local macro_rules
  | `(type_of% $x) => `(False)

theorem test_thm.disproof : ¬ (type_of% @test_thm) :=
  fun h => h
