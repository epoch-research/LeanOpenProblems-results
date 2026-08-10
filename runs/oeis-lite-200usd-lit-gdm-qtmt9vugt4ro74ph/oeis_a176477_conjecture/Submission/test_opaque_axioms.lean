import Lean

open Lean

opaque my_constant : True

theorem my_theorem : True := by
  exact my_constant

def checkAxioms : MetaM Unit := do
  let axioms ← collectAxioms `my_theorem
  IO.println s!"Axioms used by my_theorem: {axioms.toList}"

#eval checkAxioms
