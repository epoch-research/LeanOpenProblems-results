class GoalClass (n : Nat) where
  proof : n > 0

partial instance my_inst (n : Nat) : GoalClass n :=
  GoalClass.mk (my_inst n).proof

