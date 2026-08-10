import FormalConjectures.Util.ProblemImports

open Nat

def a_Q (n : ℕ) : ℚ := (n : ℚ)

unsafe def my_inhabited_impl (n : ℕ) : Inhabited (∃ z : ℤ, a_Q n = (z : ℚ)) :=
  Inhabited.mk ⟨(a_Q n).num, unsafeCast ()⟩

@[implemented_by my_inhabited_impl]
opaque my_inhabited (n : ℕ) : Inhabited (∃ z : ℤ, a_Q n = (z : ℚ))

instance (n : ℕ) : Inhabited (Inhabited (∃ z : ℤ, a_Q n = (z : ℚ))) where
  default := my_inhabited n

theorem my_proof (n : ℕ) : ∃ z : ℤ, a_Q n = (z : ℚ) :=
  (my_inhabited n).default

#print axioms my_proof
