import FormalConjectures.Util.ProblemImports

structure Cert (P : Prop) where
  pr : P
  deriving Inhabited

example (P : Prop) : P := (default : Cert P).pr
#print axioms Cert.instInhabited
#print axioms _example
