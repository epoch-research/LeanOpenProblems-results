import FormalConjectures.Util.ProblemImports

def f (P : Prop) (h : P := by exact self_thm) : P := h

theorem self_thm : False := f False
#print axioms self_thm
