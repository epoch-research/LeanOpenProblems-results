import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.startsWith "FormalConjectures" || s.startsWith "Google" || s.startsWith "Nat." then
      try
        let ax ← (Lean.Meta.getConstInfo n).run' {} |>.run {} -- won't work in Command? 
        pure ()
      catch _ => pure ()
  logInfo "done"
