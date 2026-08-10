import FormalConjectures.Util.ProblemImports

set_option autoImplicit false

theorem arb1 (P : Prop) (h : P := by exact arb2 P) : P := h

theorem arb2 (P : Prop) : P := arb1 P

#print axioms arb1
#print axioms arb2
