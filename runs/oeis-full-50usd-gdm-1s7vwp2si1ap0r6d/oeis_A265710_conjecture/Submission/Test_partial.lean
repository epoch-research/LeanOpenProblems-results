import FormalConjectures.Util.ProblemImports

inductive MyProp : Prop where
  | intro : (MyProp → False) → MyProp
