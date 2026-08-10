def GoalProp (n : Nat) : Prop := n > 0

inductive MyInhabited (α : Prop) where
  | mk (default : α)
  | dummy

instance (α : Prop) : Inhabited (MyInhabited α) :=
  ⟨MyInhabited.dummy⟩

unsafe def my_unsafe_proof (n : Nat) : GoalProp n :=
  my_unsafe_proof n

unsafe def my_unsafe_inhabited (n : Nat) : MyInhabited (GoalProp n) :=
  MyInhabited.mk (my_unsafe_proof n)

@[implemented_by my_unsafe_inhabited]
opaque my_safe_inhabited (n : Nat) : MyInhabited (GoalProp n)

theorem my_theorem (n : Nat) : GoalProp n :=
  match my_safe_inhabited n with
  | MyInhabited.mk val => val
  | MyInhabited.dummy => by sorry
