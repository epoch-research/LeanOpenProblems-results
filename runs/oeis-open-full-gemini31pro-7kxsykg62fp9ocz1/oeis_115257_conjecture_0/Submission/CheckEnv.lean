import Submission.Spec
import Lean

open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  let decl := env.find? ``oeis_115257_conjecture_0.disproof
  if let some d := decl then
    IO.println (← ppExpr d.type)
    IO.println (← ppExpr d.value!)
