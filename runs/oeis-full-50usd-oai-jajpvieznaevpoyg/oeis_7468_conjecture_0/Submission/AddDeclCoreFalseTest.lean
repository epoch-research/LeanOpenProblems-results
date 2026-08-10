import FormalConjectures.Util.ProblemImports
open Lean Elab Command

#check Environment.addDeclCore

elab "add_bad_core" : command => do
  let decl : Declaration := .thmDecl { name := `badCore, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  liftCoreM <| do
    let env ← getEnv
    let env' ← ofExceptKernelException <| env.addDeclCore (Core.getMaxHeartbeats (← getOptions)).toUSize decl (← read).cancelTk? false
    setEnv env'

add_bad_core
#print axioms badCore
#check badCore
