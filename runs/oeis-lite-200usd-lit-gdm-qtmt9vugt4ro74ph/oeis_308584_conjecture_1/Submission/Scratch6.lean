def GoalProp (n : Nat) : Prop := n > 0

opaque my_opaque_proof (n : Nat) (hn : n > 0) : GoalProp n
