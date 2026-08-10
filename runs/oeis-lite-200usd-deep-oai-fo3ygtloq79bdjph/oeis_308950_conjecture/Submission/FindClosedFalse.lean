import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term

elab "#findClosedFalse" : command => liftTermElabM do
  let env ← getEnv
  let arrRef ← IO.mkRef (#[] : Array (Name × Expr))
  for (n, ci) in env.constants.toList do
    try
      forallTelescope ci.type fun xs body => do
        if body == Lean.mkConst `False then
          try synthesizeSyntheticMVarsNoPostponing catch _ => pure ()
          let mut hasMVar := false
          for x in xs do
            if (← instantiateMVars x).hasExprMVar then hasMVar := true
          if !hasMVar then arrRef.modify (·.push (n, ci.type))
    catch _ => pure ()
  let arr ← arrRef.get
  for x in arr[:min arr.size 200] do logInfo m!"{x.1} : {x.2}"
  logInfo m!"found {arr.size}"
#findClosedFalse
