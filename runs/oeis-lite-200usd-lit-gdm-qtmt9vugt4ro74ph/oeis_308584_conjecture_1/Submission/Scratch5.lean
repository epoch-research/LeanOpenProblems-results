def GoalProp : Prop := ∀ (n : Nat), n > 0 → n > 0

theorem my_theorem (d : Nat) : GoalProp :=
  match d with
  | 0 => fun n hn => hn
  | d + 1 => my_theorem d

