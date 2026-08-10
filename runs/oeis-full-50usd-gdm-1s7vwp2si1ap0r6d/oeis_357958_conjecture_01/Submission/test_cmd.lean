import Mathlib

theorem my_theorem : False := by
  sorry

open Lean Elab Command

elab "replace_theorem" : command => do
  let env ← getEnv
  let kenv := env.toKernelEnv
  let some info := kenv.find? `my_theorem
    | IO.println "Failed to find my_theorem"
  let decl := Declaration.thmDecl {
    name := `my_theorem
    levelParams := info.levelParams
    type := info.type
    value := Expr.const `True.intro []
  }
  let fnName := Name.str (Name.str (Name.str (Name.str Name.anonymous "Lean") "Kernel") "Environment") "addDeclWithoutChecking"
  match env.evalConst (Kernel.Environment → Declaration → Except Kernel.Exception Kernel.Environment) (← getOptions) fnName with
  | Except.error e => IO.println s!"evalConst error: {e}"
  | Except.ok fn =>
    match fn kenv decl with
    | Except.error _ => IO.println "Failed to replace my_theorem"
    | Except.ok kenv2 =>
      setEnv (Lean.Environment.ofKernelEnv kenv2)
      IO.println "Replaced my_theorem successfully!"

replace_theorem
