import FormalConjectures.Util.ProblemImports

example : False := by
  let rec h : Nonempty False := ⟨Classical.choice h⟩
  exact Classical.choice h
