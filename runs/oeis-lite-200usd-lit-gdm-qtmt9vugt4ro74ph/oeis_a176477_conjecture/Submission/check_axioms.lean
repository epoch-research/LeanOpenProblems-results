import Submission.Spec
import Lean

open Lean

def checkAxioms : MetaM Unit := do
  let env ← getEnv
  let constInfo ← getConstInfo `oeis_a176477_conjecture
  let axioms := env.findUsedAxioms `oeis_a176477_conjecture
  IO.println s!"Axioms used by oeis_a176477_conjecture: {axioms}"

#eval checkAxioms
