class Unsound (α : Type) (β : outParam Type) where
  val : β

instance unsound_inst (α : Type) [Unsound α β] : Unsound α β where
  val := Unsound.val (α := α)

def unsound : Empty := Unsound.val (α := Unit)






