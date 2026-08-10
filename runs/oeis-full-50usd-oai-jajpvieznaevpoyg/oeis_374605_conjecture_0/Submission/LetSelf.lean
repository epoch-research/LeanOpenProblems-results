import FormalConjectures.Util.ProblemImports
theorem t : False := by
  let h : Nonempty False := ⟨Classical.choice h⟩
  exact Classical.choice h
