import FormalConjectures.Util.ProblemImports

structure Cert (P : Prop) where
  n : Nat
  pf : P
deriving Nonempty

#check Cert.instNonempty
#print axioms Cert.instNonempty

partial def cert (P : Prop) : Cert P := cert P
#print axioms cert
example (P : Prop) : P := (cert P).pf
#print axioms DeriveNonemptyExp._example_1
