import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 5000000
open Lean Elab Command Meta

elab "#scan_inhab_false" : command => liftTermElabM <| do
  let ref ← IO.mkRef (#[] : Array Name)
  for (n, ci) in (← getEnv).constants.toList do
    try
      forallTelescopeReducing ci.type fun xs body => do
        if body.isConstOf ``False then
          let mut ok := true
          for x in xs do
            let ty ← inferType x
            try
              discard <| synthInstance (mkApp (mkConst ``Inhabited [← getLevel ty]) ty)
            catch _ => ok := false
          if ok then ref.modify (·.push n)
    catch _ => pure ()
  let found ← ref.get
  logInfo m!"found {found.size}: {found.extract 0 (min found.size 200)}"
#scan_inhab_false
