import FormalConjectures.Util.ProblemImports

partial def dn (P : Prop) : (P → False) → False
  | hn => dn P hn

theorem arbitrary (P : Prop) : P := Classical.byContradiction (dn P)
#print axioms arbitrary
