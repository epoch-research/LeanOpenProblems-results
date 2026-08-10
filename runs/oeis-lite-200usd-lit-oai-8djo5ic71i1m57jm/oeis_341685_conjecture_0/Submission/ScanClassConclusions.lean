import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let needles := ["Subsingleton ", "Fintype ", "Finite ", "IsEmpty ", "Unique ", "Nontrivial ", "Infinite "]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      try
        liftTermElabM <| forallTelescope ti.type fun xs b => do
          let s := toString b
          if needles.any (fun nd => s.contains nd) then
            logInfo m!"{n} : {ti.type} ==> {b}"
      catch _ => pure ()
    | _ => pure ()
