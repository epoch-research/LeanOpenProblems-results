import Submission.Spec
import Lean

open Lean

def main : IO Unit := do
  let env ← importModules #[{ module := `Submission.Spec }] {}
  let decl := env.find? `A096535_occurs_infinitely_often.disproof
  match decl with
  | some (ConstantInfo.thmInfo info) =>
    IO.println "Disproof found!"
    IO.println (toString info.type)
    IO.println (info.value.hasExprMVar)
  | _ => IO.println "Not found"
