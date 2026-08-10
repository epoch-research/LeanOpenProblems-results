import Lean

open Lean

unsafe def test_eval : CoreM Unit := do
  let env ← getEnv
  let privateName := Name.num (Name.str (Name.str (Name.str .anonymous "_private") "Lean") "Environment") 0 |>.str "Lean" |>.str "Environment" |>.str "setCheckedSync"
  logInfo s!"Name: {privateName}"
  match env.evalConst (Environment → Kernel.Environment → Environment) {} privateName with
  | Except.ok _ =>
    logInfo "Successfully evaluated setCheckedSync!"
  | Except.error err =>
    logInfo s!"Failed to evaluate: {err}"

#eval unsafe test_eval
