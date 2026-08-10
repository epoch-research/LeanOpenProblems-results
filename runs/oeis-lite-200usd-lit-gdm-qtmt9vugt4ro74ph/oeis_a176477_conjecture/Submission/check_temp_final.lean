import Submission.Spec_temp_final
import Lean

open Lean

def check : MetaM Unit := do
  let env ← getEnv
  let axioms ← collectAxioms `oeis_a176477_conjecture
  IO.println s!"Axioms: {axioms.toList}"

#eval check
