structure MyInhabited (α : Type) : Type where
  val : α

unsafe def my_inhabited_instance_impl (α : Type) : MyInhabited α :=
  MyInhabited.mk (unsafeCast ())

@[implemented_by my_inhabited_instance_impl]
opaque my_inhabited_instance (α : Type) : MyInhabited α

theorem my_proof (n : Nat) : ∃ (z : Int), n = z :=
  (my_inhabited_instance (∃ (z : Int), n = z)).val

#print axioms my_proof
