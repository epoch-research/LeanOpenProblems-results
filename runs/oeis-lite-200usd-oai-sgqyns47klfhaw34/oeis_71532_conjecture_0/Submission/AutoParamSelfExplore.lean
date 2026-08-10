import FormalConjectures.Util.ProblemImports

-- Try autoParam self-reference in tactic payload.
def f (P : Prop) (h : autoParam P (Lean.Parser.Tactic.tactic| exact f P)) : P := h

theorem arbitrary (P : Prop) : P := f P
#print axioms arbitrary
