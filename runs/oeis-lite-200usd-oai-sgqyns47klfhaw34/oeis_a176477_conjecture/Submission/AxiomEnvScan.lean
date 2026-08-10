import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst
  let mut count := 0
  for n in names do
    if (toString n).startsWith "FormalConjectures" || (toString n).contains "flagged_by_linter" then
      try
        let axs ← (Lean.Meta.getUsedAxioms n).run' {}
        if axs.any (· == `sorryAx) then
          IO.println s!"sorry dep: {n}"
          count := count + 1
          if count > 50 then break
      catch _ => pure ()
  IO.println s!"count {count}"
