import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs

def a_Q (n : ℕ) : ℚ := (n : ℚ)

inductive MyInhabitedClass (α : Type) : Type where
  | mk (val : α) : MyInhabitedClass α
  | dummy : MyInhabitedClass α

instance (α : Type) : Inhabited (MyInhabitedClass α) where
  default := MyInhabitedClass.dummy

unsafe def my_inhabited_class_impl (n : ℕ) : MyInhabitedClass (PLift (∃ z : ℤ, a_Q n = (z : ℚ))) :=
  MyInhabitedClass.mk (PLift.up ⟨(a_Q n).num, unsafeCast ()⟩)

@[implemented_by my_inhabited_class_impl]
partial def my_inhabited_class (n : ℕ) : MyInhabitedClass (PLift (∃ z : ℤ, a_Q n = (z : ℚ))) :=
  my_inhabited_class n

noncomputable instance inst (n : ℕ) : Inhabited (PLift (∃ z : ℤ, a_Q n = (z : ℚ))) where
  default :=
    match my_inhabited_class n with
    | MyInhabitedClass.mk val => val
    | MyInhabitedClass.dummy => @inst n |>.default

theorem a_Q_int_test (n : ℕ) : ∃ z : ℤ, a_Q n = (z : ℚ) :=
  (inst n).default.down

#print axioms a_Q_int_test
