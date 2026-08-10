import Mathlib

class MyInhabited (α : Type) where
  val : α

mutual
  opaque default_myinhabited (α : Type) : MyInhabited α
  instance (α : Type) : Inhabited (MyInhabited α) := ⟨default_myinhabited α⟩
end
