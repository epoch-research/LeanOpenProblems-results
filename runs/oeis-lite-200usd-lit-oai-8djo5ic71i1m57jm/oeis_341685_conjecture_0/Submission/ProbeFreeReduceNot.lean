import FormalConjectures.Util.ProblemImports

#check FreeGroup.reduce.not
#check FreeAddGroup.reduce.not
#check FreeGroup.reduce
#check FreeAddGroup.reduce

-- Can we craft a reducible equality `reduce L = ... ++ (x,b)::(x,!b)::...`?
example : False := by
  -- `reduce` should remove adjacent inverse pairs, so this should be impossible.
  -- test no accidental rfl.
  fail_if_success exact FreeGroup.reduce.not (α := Bool) (P := False) (L₁ := [(true,true),(true,false)]) (L₂ := []) (L₃ := []) (x := true) (b := true) rfl
  sorry

example : False := by
  fail_if_success exact FreeAddGroup.reduce.not (α := Bool) (P := False) (L₁ := [(true,true),(true,false)]) (L₂ := []) (L₃ := []) (x := true) (b := true) rfl
  sorry
