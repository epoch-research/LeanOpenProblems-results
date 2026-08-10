import FormalConjectures.Util.ProblemImports

structure Cert (P : Prop) where
  n : Nat
  pf : P

partial def cert1 (P : Prop) : Cert P := cert1 P
#print axioms cert1

example (P : Prop) : P := (cert1 P).pf
#print axioms PartialStructExp._example_1

structure Cert2 (P : Prop) where
  pf : P

partial def cert2 (P : Prop) : Cert2 P := cert2 P
#print axioms cert2
example (P : Prop) : P := (cert2 P).pf
#print axioms PartialStructExp._example_2
