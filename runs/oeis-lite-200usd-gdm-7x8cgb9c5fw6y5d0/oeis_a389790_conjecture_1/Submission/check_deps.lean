import Mathlib.Data.Nat.Basic
import Lean

open Lean

theorem my_proof : True := by sorry

def checkDeps : CoreM Unit := do
  let env ← getEnv
  match env.find? `my_proof with
  | some (.thmInfo val) =>
    IO.println s!"Repr: {repr val.value}"
  | _ => IO.println "Not found"

#eval! checkDeps
