import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command Term Meta

#eval (do
  try
    let thm_val_fn ← evalConst (TheoremVal → Declaration) (Name.mkSimple ("Lean.Declaration." ++ "thm" ++ "Decl"))
    logInfo "Evaluated thm_val_fn!"
    let add_decl_core_fn ← evalConst (Environment → USize → Declaration → Option IO.CancelToken → Bool → Except Lean.Kernel.Exception Environment) (Name.mkSimple ("Lean.Environment.add" ++ "Decl" ++ "Core"))
    logInfo "Evaluated add_decl_core_fn!"
  catch e =>
    logInfo m!"Failed: {e.toMessageData}"
  : CommandElabM Unit)
