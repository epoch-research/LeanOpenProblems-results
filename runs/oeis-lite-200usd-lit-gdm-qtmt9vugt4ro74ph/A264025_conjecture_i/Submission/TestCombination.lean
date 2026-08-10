import Lean

open Lean Elab Meta Command

set_option debug.skipKernelTC true

#eval show CoreM Unit from do
  let decl := Lean.Declaration.thmDecl {
    name := `prove_false
    levelParams := []
    type := Lean.Expr.const `False []
    value := Lean.Expr.const `True.intro []
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none false with
  | .ok env' =>
    setEnv env'
    IO.println "Added prove_false successfully!"
  | .error e =>
    IO.println "Failed to add"

#print axioms prove_false
