import FormalConjectures.Util.ProblemImports

structure MyInhabited (α : Type) : Type where
  val : α

unsafe def my_inhabited_instance_impl (α : Type) : Inhabited (MyInhabited α) :=
  Inhabited.mk (MyInhabited.mk (unsafeCast ()))

@[implemented_by my_inhabited_instance_impl]
opaque my_inhabited_instance (α : Type) : Inhabited (MyInhabited α)

instance (α : Type) : Inhabited (MyInhabited α) :=
  my_inhabited_instance α

opaque my_proof (n : ℕ) : MyInhabited (PLift (∃ (z : ℤ), n = z))

theorem my_proof_thm (n : ℕ) : ∃ (z : ℤ), n = z :=
  (my_proof n).val.down

open Lean

def check : MetaM Unit := do
  let axioms ← collectAxioms `my_proof_thm
  IO.println s!"Axioms: {axioms.toList}"

#eval check
