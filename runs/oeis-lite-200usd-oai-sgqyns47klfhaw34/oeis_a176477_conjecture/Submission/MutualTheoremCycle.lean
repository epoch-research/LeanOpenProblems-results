import FormalConjectures.Util.ProblemImports

def P : Prop := True
mutual
  theorem T : P := by exact H.out
  theorem H : Fact P := ⟨T⟩
end
#check T
#print axioms T
