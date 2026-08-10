import Submission.Spec
import Lean

open Lean

def check : MetaM Unit := do
  let axioms1 ← collectAxioms `oeis_a176477_conjecture
  IO.println s!"Conjecture Axioms: {axioms1.toList}"
  let axioms2 ← collectAxioms `a_Q_int
  IO.println s!"a_Q_int Axioms: {axioms2.toList}"

#eval check
