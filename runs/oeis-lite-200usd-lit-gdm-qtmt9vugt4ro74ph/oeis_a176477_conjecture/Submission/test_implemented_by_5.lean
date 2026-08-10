import Mathlib

structure MyInhabited (α : Type) : Type where
  val : α

unsafe def my_inhabited_instance_impl (α : Type) : Inhabited (MyInhabited α) :=
  Inhabited.mk (MyInhabited.mk (unsafeCast ()))

@[implemented_by my_inhabited_instance_impl]
opaque my_inhabited_instance (α : Type) : Inhabited (MyInhabited α)

instance (α : Type) : Inhabited (MyInhabited α) :=
  my_inhabited_instance α

opaque my_proof (n : ℕ) : MyInhabited (PLift (∃ (z : ℤ), n = z))

#print axioms my_proof
