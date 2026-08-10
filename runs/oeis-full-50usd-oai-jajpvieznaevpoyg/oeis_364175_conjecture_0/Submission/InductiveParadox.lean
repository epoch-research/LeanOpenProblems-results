import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| intro : (Bad → False) → Bad

theorem bad_false : False := by
  let b : Bad := Bad.intro (fun x => ?_)
  exact ?_
