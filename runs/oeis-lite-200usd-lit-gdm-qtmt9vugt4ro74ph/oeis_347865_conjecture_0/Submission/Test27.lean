import FormalConjectures.Util.ProblemImports

inductive T : Type where
  | mk (x : T) : T

partial def loop_t (u : Unit) : T :=
  loop_t u
