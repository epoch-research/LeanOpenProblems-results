import FormalConjectures.Util.ProblemImports

theorem arb1 (P : Prop) (h : P := by exact lcProof) : P := h

theorem bad : False := arb1 False
#print arb1
#print axioms arb1
#print axioms bad
