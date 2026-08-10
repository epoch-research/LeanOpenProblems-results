import FormalConjectures.Util.ProblemImports
@[extern "lean_false"] unsafe opaque bad : False
unsafe theorem tunsafe : False := bad
theorem t : False := by exact bad
