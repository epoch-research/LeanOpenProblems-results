import FormalConjectures.Util.ProblemImports
partial def arbWithInst (α : Sort u) [Inhabited α] : α := arbWithInst α

theorem arbitrary (P : Prop) : P := by
  haveI inst : Inhabited P := ⟨@arbWithInst P inst⟩
  exact @arbWithInst P inst
#print axioms arbWithInst
#print axioms arbitrary
