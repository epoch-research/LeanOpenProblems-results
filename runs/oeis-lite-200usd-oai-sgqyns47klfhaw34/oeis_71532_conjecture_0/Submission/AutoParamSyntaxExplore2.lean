import FormalConjectures.Util.ProblemImports

macro "my_tac" : tactic => `(tactic| exact trivial)

def g (h : autoParam True (by my_tac)) : True := h
#check g
example : True := g

-- now self tactic macro
macro "self_tac" : tactic => `(tactic| exact f _)
def f (P : Prop) (h : autoParam P (by self_tac)) : P := h

theorem arbitrary (P : Prop) : P := f P
#print axioms arbitrary
