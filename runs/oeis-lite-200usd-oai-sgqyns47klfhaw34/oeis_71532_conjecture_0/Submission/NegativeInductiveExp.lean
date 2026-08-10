import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| intro : (Bad → False) → Bad
example : False := by
  let nb : Bad → False := fun b => match b with | .intro f => f b
  exact nb (.intro nb)
#print axioms NegativeInductiveExp._example_1
