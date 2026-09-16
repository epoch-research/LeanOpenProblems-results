import Lean
import Submission.Spec

open Lean

def isSorryAx (e : Expr) : Bool :=
  e.isConstOf ``sorryAx

def containsSorry (e : Expr) : Bool :=
  Option.isSome <| e.find? (fun e' => isSorryAx e')

def main : IO Unit := do
  let env ← importModules #[{ module := `Submission.Spec }] {}
  let some info := env.find? `oeis_a361714_conjecture_2.disproof
    | IO.println "Not found"
  let val := info.value!
  IO.println s!"Has sorry? {containsSorry val}"
