import FormalConjectures.Util.ProblemImports

mutual
  theorem arb1 (P : Prop) (h : P := arb2 P) : P := h
  theorem arb2 (P : Prop) (h : P := arb1 P) : P := h
end

#print axioms arb1
#print axioms arb2
