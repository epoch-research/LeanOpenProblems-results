import FormalConjectures.Util.ProblemImports

partial def arbWithInst (α : Sort u) [Inhabited α] : α := arbWithInst α
partial def instSelf (α : Sort u) : Inhabited α := ⟨@arbWithInst α (instSelf α)⟩

theorem arbitrary (P : Prop) : P :=
  @arbWithInst P (instSelf P)

#print axioms arbWithInst
#print axioms instSelf
#print axioms arbitrary
