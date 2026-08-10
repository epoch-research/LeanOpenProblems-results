import FormalConjectures.Util.ProblemImports

inductive MyType : Type where
  | mk (A : Prop) : MyType

def lift (x : MyType) : Prop :=
  match x with
  | .mk A => A

#print MyType
#print lift
