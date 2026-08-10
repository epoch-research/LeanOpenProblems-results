import FormalConjectures.Util.ProblemImports

#check FreeGroup.reduce.not
#check FreeGroup.reduce
#eval FreeGroup.reduce [(0, true), (0, false)]
#eval FreeGroup.reduce [(0, true), (1, false), (1, true), (0, false)]

example : False := by
  exact FreeGroup.reduce.not (α := ℕ) (p := False) (L₁ := [(0,true),(0,false)]) (L₂ := []) (L₃ := []) (x := 0) (b := true) rfl

example : False := by
  exact FreeAddGroup.reduce.not (α := ℕ) (p := False) (L₁ := [(0,true),(0,false)]) (L₂ := []) (L₃ := []) (x := 0) (b := true) rfl
