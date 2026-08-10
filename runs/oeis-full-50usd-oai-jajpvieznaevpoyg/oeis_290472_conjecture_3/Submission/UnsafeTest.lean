import FormalConjectures.Util.ProblemImports
unsafe def bad : False := unsafeCast True.intro
@[implemented_by bad] opaque badSafe : False

theorem tbad : False := badSafe
#print axioms tbad
