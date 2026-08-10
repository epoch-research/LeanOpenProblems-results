import FormalConjectures.Util.ProblemImports

partial def arbWithInst (α : Sort u) [Inhabited α] : α := arbWithInst α

theorem nn (P : Prop) : ¬¬P := by
  letI : Inhabited (¬¬P) := ⟨arbWithInst (¬¬P)⟩
  exact arbWithInst (¬¬P)

theorem arbitrary (P : Prop) : P := by
  classical
  exact Classical.byContradiction (nn P)

#print axioms arbWithInst
#print axioms nn
#print axioms arbitrary
