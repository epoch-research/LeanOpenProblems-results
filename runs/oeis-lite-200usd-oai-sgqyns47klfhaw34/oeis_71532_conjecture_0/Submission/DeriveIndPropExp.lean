import FormalConjectures.Util.ProblemImports
inductive Cert (P : Prop) : Prop where
| mk : P → Cert P
deriving Nonempty
#check Cert.instNonempty
#print axioms Cert.instNonempty
example (P : Prop) : P := by
  have h : Cert P := Classical.choice (Cert.instNonempty P)
  cases h with | mk p => exact p
#print axioms DeriveIndPropExp._example_1
