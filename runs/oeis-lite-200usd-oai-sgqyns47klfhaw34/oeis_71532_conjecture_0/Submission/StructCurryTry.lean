import FormalConjectures.Util.ProblemImports

structure BadStruct : Prop where
  elim : BadStruct → False

example : False := by
  let b : BadStruct := ⟨fun x => x.elim x⟩
  exact b.elim b
