import Lean

open Lean Elab Command Term Meta

#eval (do
  try
    let add_decl_core_fn ← liftTermElabM <| evalConst (Environment → USize → Declaration → Option IO.CancelToken → Bool → Except Kernel.Exception Environment) `Lean.Environment.addDeclCore
    logInfo "Evaluated add_decl_core_fn successfully!"
    let thm_decl_fn ← liftTermElabM <| evalConst (TheoremVal → Declaration) `Lean.Declaration.thmDecl
    logInfo "Evaluated thm_decl_fn successfully!"
  catch e =>
    logInfo m!"Failed: {e.toMessageData}"
  : CommandElabM Unit)
