import Submission.test_comp
import Lean

open Lean

def checkAxioms : MetaM Unit := do
  let env ← getEnv
  let axioms := env.findUsedAxioms `test_opaque
  IO.println s!"AXIOMS: {axioms}"

#eval checkAxioms
