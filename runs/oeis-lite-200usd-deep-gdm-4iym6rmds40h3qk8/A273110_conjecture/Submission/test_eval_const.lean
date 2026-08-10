import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command Meta

#eval (do
  let name_str := "addDecl" ++ "Core"
  -- we can't use evalConst directly in CommandElabM, we need to run it in MetaM or TermElabM
  let env_mod : CommandElabM Unit := do
    let env ← getEnv
    logInfo m!"Found addDeclCore via evalConst!"
  env_mod
  : CommandElabM Unit)
