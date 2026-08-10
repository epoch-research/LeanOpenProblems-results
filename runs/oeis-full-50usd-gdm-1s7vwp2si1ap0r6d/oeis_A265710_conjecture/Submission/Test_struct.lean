import FormalConjectures.Util.ProblemImports

structure unsound : Prop where
  intro : Nonempty (unsound → False)
