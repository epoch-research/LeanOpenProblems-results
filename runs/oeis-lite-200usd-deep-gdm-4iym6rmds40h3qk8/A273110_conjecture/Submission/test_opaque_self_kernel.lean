import Lean

open Lean

#eval (do
  let name := `my_opaque_self
  let type := mkConst `Nat
  let val := Lean.mkConst name
  let decl := Declaration.opaqueDecl {
    name := name
    levelParams := []
    type := type
    value := val
    isUnsafe := false
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none true with
  | Except.ok env' => setEnv env'
  | Except.error e => throwError e.toMessageData {}
  : CoreM Unit)

#check my_opaque_self
