import Spec
import Lean

open Lean

def printAxioms (declName : Name) : MetaM Unit := do
  let env ← getEnv
  let some info := env.find? declName | return
  let (_, axioms) ← (Elab.Command.collectAxioms declName).run'
  IO.println s!"Axioms for {declName}: {axioms.toList}"

#eval printAxioms `oeis_248802_conjecture_0
