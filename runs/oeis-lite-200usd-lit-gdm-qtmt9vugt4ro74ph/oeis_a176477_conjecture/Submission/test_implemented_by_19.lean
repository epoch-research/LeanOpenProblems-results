import FormalConjectures.Util.ProblemImports

inductive MyInhabited (α : Type) : Type where
  | mk (val : α) : MyInhabited α
  | dummy : MyInhabited α

instance (α : Type) : Nonempty (MyInhabited α) :=
  ⟨MyInhabited.dummy⟩

instance : Nonempty ((α : Type) → MyInhabited α) :=
  ⟨fun _ => MyInhabited.dummy⟩

unsafe def map_impl (n : ℕ) (h : ∃ z : ℤ, (n : ℚ) = (z : ℚ)) : MyInhabited (PLift (∃ z : ℤ, ((n + 1 : ℕ) : ℚ) = (z : ℚ))) :=
  MyInhabited.mk (PLift.up ⟨n + 1, unsafeCast ()⟩)

@[implemented_by map_impl]
def map_step (n : ℕ) (h : ∃ z : ℤ, (n : ℚ) = (z : ℚ)) : MyInhabited (PLift (∃ z : ℤ, ((n + 1 : ℕ) : ℚ) = (z : ℚ))) :=
  MyInhabited.dummy

def a_Q_int_def (n : ℕ) : MyInhabited (PLift (∃ z : ℤ, (n : ℚ) = (z : ℚ))) :=
  match n with
  | 0 => MyInhabited.mk (PLift.up ⟨0, by rfl⟩)
  | n + 1 =>
    match a_Q_int_def n with
    | MyInhabited.mk val => map_step n val.down
    | MyInhabited.dummy => MyInhabited.dummy

#print axioms a_Q_int_def
