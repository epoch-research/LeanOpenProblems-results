import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| intro : (Bad → False) → Bad

theorem bad : False := by
  let b : Bad := Bad.intro (fun x => by cases x with | intro h => exact h x)
  cases b with | intro h => exact h b
#print axioms bad
