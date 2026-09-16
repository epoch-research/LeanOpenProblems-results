import Submission.Test24
import Lean

open Lean

def main : IO Unit := do
  let env ← importModules #[{ module := `Submission.Test24 }] {}
  let decl := env.find? `A096535_occurs_infinitely_often.disproof
  match decl with
  | some (ConstantInfo.thmInfo info) =>
    IO.println "Disproof found!"
    IO.println (toString info.type)
  | _ => IO.println "Not found"
