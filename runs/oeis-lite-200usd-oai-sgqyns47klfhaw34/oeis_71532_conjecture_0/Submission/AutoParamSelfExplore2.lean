import FormalConjectures.Util.ProblemImports

def g (h : True := by exact trivial) : True := h
example : True := g

-- The tactic is stored and should run at call sites. Can it refer to f?
def f (P : Prop) (h : P := by exact f P) : P := h

theorem arbitrary (P : Prop) : P := f P
#print axioms arbitrary
#print f
