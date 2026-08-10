import Lean

open Lean

unsafe def test_add : CoreM Unit := do
  let env ← getEnv
  let privateName := Name.num (Name.str (Name.str (Name.str .anonymous "_private") "Lean") "Environment") 0 |>.str "Lean" |>.str "Kernel" |>.str "Environment" |>.str "add"
  logInfo s!"Name: {privateName}"
  match env.evalConst (Kernel.Environment → ConstantInfo → Kernel.Environment) {} privateName with
  | Except.ok _ =>
    logInfo "Successfully evaluated Kernel.Environment.add!"
  | Except.error err =>
    logInfo s!"Failed: {err}"

#eval unsafe test_add
