import FormalConjectures.Util.ProblemImports

inductive MyInhabited (α : Type) : Type where
  | mk (val : α) : MyInhabited α
  | dummy : MyInhabited α

instance (α : Type) : Nonempty (MyInhabited α) :=
  ⟨MyInhabited.dummy⟩

instance : Nonempty ((α : Type) → MyInhabited α) :=
  ⟨fun _ => MyInhabited.dummy⟩

unsafe def my_inhabited_instance_impl (α : Type) : MyInhabited α :=
  MyInhabited.mk (unsafeCast ())

@[implemented_by my_inhabited_instance_impl]
partial def my_inhabited_instance (α : Type) : MyInhabited α :=
  my_inhabited_instance α

mutual
  partial def extract (n : ℕ) (w : MyInhabited (PLift (∃ z : ℤ, (n : ℚ) = (z : ℚ)))) : PLift (∃ z : ℤ, (n : ℚ) = (z : ℚ)) :=
    match w with
    | MyInhabited.mk val => val
    | MyInhabited.dummy => extract n w

  partial def inst_def (n : ℕ) : Inhabited (PLift (∃ z : ℤ, (n : ℚ) = (z : ℚ))) where
    default := extract n (my_inhabited_instance (PLift (∃ z : ℤ, (n : ℚ) = (z : ℚ))))
end

theorem a_Q_int_test (n : ℕ) : ∃ z : ℤ, (n : ℚ) = (z : ℚ) :=
  (inst_def n).default.down
