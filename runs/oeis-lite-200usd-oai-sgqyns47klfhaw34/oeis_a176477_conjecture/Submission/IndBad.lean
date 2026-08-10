import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| mk : (Bad -> False) -> Bad

theorem badFalse : False := by
  let b : Bad := Bad.mk (fun x => ?_)
  exact ?_
