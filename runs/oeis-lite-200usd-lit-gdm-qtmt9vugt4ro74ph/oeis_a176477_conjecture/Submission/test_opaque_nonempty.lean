import FormalConjectures.Util.ProblemImports

def a_Q (n : ℕ) : ℚ := (n : ℚ)

opaque my_nonempty (n : ℕ) : Nonempty (∃ (z : ℤ), a_Q n = (z : ℚ))

theorem a_Q_int_test (n : ℕ) : ∃ (z : ℤ), a_Q n = (z : ℚ) :=
  Classical.choice (my_nonempty n)

open Lean

def check : MetaM Unit := do
  let axioms ← collectAxioms `a_Q_int_test
  IO.println s!"Axioms used by a_Q_int_test: {axioms.toList}"

#eval check
