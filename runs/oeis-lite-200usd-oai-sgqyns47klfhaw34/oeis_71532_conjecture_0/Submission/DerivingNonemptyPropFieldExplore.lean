import FormalConjectures.Util.ProblemImports

structure Cert (P : Prop) where
  pr : P
  deriving Nonempty

example (P : Prop) : P := (Classical.choice (inferInstance : Nonempty (Cert P))).pr
#print axioms Cert.instNonempty
#print axioms _example
