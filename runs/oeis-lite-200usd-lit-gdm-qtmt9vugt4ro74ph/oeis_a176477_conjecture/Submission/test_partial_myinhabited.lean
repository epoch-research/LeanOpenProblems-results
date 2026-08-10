import FormalConjectures.Util.ProblemImports

inductive MyInhabited (α : Type) : Type where
  | mk (val : α) : MyInhabited α
  | dummy : MyInhabited α

instance (α : Type) : Nonempty (MyInhabited α) :=
  ⟨MyInhabited.dummy⟩

def a_Q (n : ℕ) : ℚ := (n : ℚ)

partial def a_Q_int_def (n : ℕ) : MyInhabited (PLift (∃ z : ℤ, a_Q n = (z : ℚ))) :=
  a_Q_int_def n
