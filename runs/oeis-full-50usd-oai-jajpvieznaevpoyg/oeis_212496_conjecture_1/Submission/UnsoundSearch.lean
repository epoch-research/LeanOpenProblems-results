import FormalConjectures.Util.ProblemImports
import Qq
open Lean Meta Elab Command Qq
#eval show CommandElabM Unit from do
  let targets : Array Expr := #[q(False), q(Nonempty False), q(Inhabited False), q(Subsingleton Prop), q(∀ P : Prop, P), q(∀ P : Prop, Nonempty P)]
  let env ← getEnv
  for target in targets do
    let mut found := 0
    for (n, ci) in env.constants.toList do
      try
        if (← liftTermElabM <| Meta.isDefEq ci.type target) then
          let ax ← collectAxioms n
          logInfo m!"TARGET {target}: {n}, axioms {ax.toList}"
          found := found + 1
          if found > 20 then break
      catch _ => pure ()
    logInfo m!"target done, found {found}"
