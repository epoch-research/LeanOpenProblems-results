import Submission.Test26
import Lean

open Lean

def main : IO Unit := do
  let env ← importModules #[{ module := `Submission.Test26 }] {}
  let decl := env.find? `A096535_occurs_infinitely_often
  match decl with
  | some (ConstantInfo.thmInfo info) =>
    IO.println "Proof found!"
    IO.println (toString info.type)
  | _ => IO.println "Not found"
