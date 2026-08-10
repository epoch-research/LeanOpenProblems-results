def GoalProp (n : Nat) : Prop := n > 0

unsafe def my_unsafe_proof (n : Nat) (hn : n > 0) [Inhabited (GoalProp n)] : GoalProp n :=
  my_unsafe_proof n hn

@[implemented_by my_unsafe_proof]
opaque my_safe_proof (n : Nat) (hn : n > 0) [Inhabited (GoalProp n)] : GoalProp n

theorem my_theorem (n : Nat) (hn : n > 0) [Inhabited (GoalProp n)] : GoalProp n :=
  my_safe_proof n hn


theorem my_theorem_call (n : Nat) (hn : n > 0) : GoalProp n :=
  have : Inhabited (GoalProp n) := ⟨hn⟩
  my_theorem n hn

#print axioms my_theorem_call

