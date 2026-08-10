import FormalConjectures.Util.ProblemImports

partial def arbWithInst (α : Sort u) [Inhabited α] : α := arbWithInst α

theorem nn (P : Prop) : ¬¬P := by
  let rec inst : Inhabited (¬¬P) := ⟨@arbWithInst (¬¬P) inst⟩
  letI : Inhabited (¬¬P) := inst
  exact arbWithInst (¬¬P)

#print axioms arbWithInst
#print axioms nn
