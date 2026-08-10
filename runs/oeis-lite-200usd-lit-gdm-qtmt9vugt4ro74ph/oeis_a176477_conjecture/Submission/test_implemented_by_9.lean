
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs

def a_Q (n : ℕ) : ℚ := (n : ℚ)

inductive MyInhabited (α : Type) : Type where
  | mk (val : α) : MyInhabited α
  | dummy : MyInhabited α

instance (α : Type) : Inhabited (MyInhabited α) where
  default := MyInhabited.dummy

unsafe def my_inhabited_instance_impl (α : Type) : MyInhabited α :=
  MyInhabited.mk (unsafeCast ())

@[implemented_by my_inhabited_instance_impl]
opaque my_inhabited_instance (α : Type) : MyInhabited α

partial def extract (n : ℕ) (w : MyInhabited (PLift (∃ z : ℤ, a_Q n = (z : ℚ)))) [inst : Inhabited (PLift (∃ z : ℤ, a_Q n = (z : ℚ)))] : PLift (∃ z : ℤ, a_Q n = (z : ℚ)) :=
  match w with
  | MyInhabited.mk val => val
  | MyInhabited.dummy => @extract n w inst

partial def inst_def (n : ℕ) : Inhabited (PLift (∃ z : ℤ, a_Q n = (z : ℚ))) where
  default := @extract n (my_inhabited_instance (PLift (∃ z : ℤ, a_Q n = (z : ℚ)))) (inst_def n)

instance inst (n : ℕ) : Inhabited (PLift (∃ z : ℤ, a_Q n = (z : ℚ))) :=
  inst_def n

theorem a_Q_int_test (n : ℕ) : ∃ z : ℤ, a_Q n = (z : ℚ) :=
  (extract n (my_inhabited_instance (PLift (∃ z : ℤ, a_Q n = (z : ℚ))))).down

#print axioms a_Q_int_test
