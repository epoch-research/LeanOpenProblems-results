open Classical

theorem test_if (f : Prop → Nat) : (if Prop = Prop then f True else 0) = f True := by
  have h : Prop = Prop := rfl
  rw [if_pos h]
