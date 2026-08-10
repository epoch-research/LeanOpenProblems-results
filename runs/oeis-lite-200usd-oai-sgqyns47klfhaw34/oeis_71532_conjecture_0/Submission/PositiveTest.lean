import FormalConjectures.Util.ProblemImports

inductive Bad (P : Prop) : Prop where
| intro : (Bad P → P) → Bad P

example (P : Prop) : P := by
  let f : Bad P → P := fun b => match b with | Bad.intro g => g b
  exact f (Bad.intro f)
