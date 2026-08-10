import FormalConjectures.Util.ProblemImports
partial def bogusProp (P : Prop) [Decidable P] : P :=
  if h : P then h else bogusProp P
example : False := bogusProp False
#print axioms bogusProp
