class Unsound (α : Type) (β : outParam Type) where
  val : β

instance base : Unsound Unit Empty where
  val := @Unsound.val Unit Empty base

def unsound : Empty := Unsound.val (α := Unit)
