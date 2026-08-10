import FormalConjectures.Util.ProblemImports
axiom P : Prop

example : P := by
  letI inst : Inhabited P := inst
  exact default

example : P := by
  let inst : Inhabited P := inst
  exact @default P inst

example : P := by
  have h : Inhabited P := h
  exact @default P h
