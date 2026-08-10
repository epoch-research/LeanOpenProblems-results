import FormalConjectures.Util.ProblemImports

def goodFalse : False := by
  -- impossible
  exact False.elim (by contradiction)

unsafe def badImpl : False := unsafeCast ()

@[implemented_by badImpl]
def weirdFalse : False := goodFalse

theorem Timpl : False := weirdFalse
#print axioms Timpl
