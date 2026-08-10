import FormalConjectures.Util.ProblemImports
partial def contrP (P : Prop) (h : ¬ P) : P := contrP P h
partial def contrF (P : Prop) (h : ¬ P) : False := h (contrP P h)
theorem arb (P:Prop) : P := Classical.byContradiction (contrF P)
#print axioms contrP
#print axioms contrF
#print axioms arb
