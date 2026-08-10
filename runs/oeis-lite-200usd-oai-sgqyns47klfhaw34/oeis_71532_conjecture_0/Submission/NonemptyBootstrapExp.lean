import FormalConjectures.Util.ProblemImports

structure Cert (P : Prop) where
  pf : P

partial def cert (P : Prop) [Nonempty (Cert P)] : Cert P := cert P
#print axioms cert

instance instCertNonempty (P : Prop) : Nonempty (Cert P) := ⟨cert P⟩
#print axioms instCertNonempty

example (P : Prop) : P := (cert P).pf
#print axioms NonemptyBootstrapExp._example_1

example (P : Prop) : P := (Classical.choice (instCertNonempty P)).pf
#print axioms NonemptyBootstrapExp._example_2
