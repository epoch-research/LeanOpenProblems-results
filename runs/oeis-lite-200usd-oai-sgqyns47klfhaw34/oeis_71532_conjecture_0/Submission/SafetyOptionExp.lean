import FormalConjectures.Util.ProblemImports
set_option checkBinderAnnotations false
set_option pp.universes true
set_option compiler.extract_closed false
-- set_option safety false

theorem t : False := by
  exact lcProof
#print axioms t
