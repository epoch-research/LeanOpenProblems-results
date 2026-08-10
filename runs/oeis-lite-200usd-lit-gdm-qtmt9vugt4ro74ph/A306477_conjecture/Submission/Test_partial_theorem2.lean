partial def my_partial (x : Nat) : Nat :=
  my_partial x

theorem test : my_partial 0 = 0 := by
  rfl
