import FormalConjectures.Util.ProblemImports

def g (h : autoParam True (tactic| exact trivial)) : True := h
#check g
example : True := g

macro "self_tac" : tactic => `(tactic| exact f _)
def f (P : Prop) (h : autoParam P (tactic| self_tac)) : P := h

theorem arbitrary (P : Prop) : P := f P
#print axioms arbitrary
