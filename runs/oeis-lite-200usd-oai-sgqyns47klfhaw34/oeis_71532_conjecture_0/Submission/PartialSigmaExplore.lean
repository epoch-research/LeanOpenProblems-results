import FormalConjectures.Util.ProblemImports

-- Try hiding proof behind a function domain that is empty under its own field.
structure W (P : Prop) where
  q : Prop
  hq : q → False
  hp : q → P

deriving instance Nonempty for W

partial def wLoop (P : Prop) : W P := wLoop P
#print axioms wLoop

-- no way to get q; but maybe choose q=False in deriving. inspect constructor?
#check W.mk
#check W.rec
