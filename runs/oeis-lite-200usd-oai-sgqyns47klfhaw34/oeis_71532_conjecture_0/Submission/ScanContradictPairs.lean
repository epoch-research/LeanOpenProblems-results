import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 3000000
open Lean Meta Elab Command

elab "#scan_contradict_pairs" : command => do
  liftTermElabM do
    let env ← getEnv
    let positivesRef ← IO.mkRef (#[] : Array (Name × Expr))
    let negsRef ← IO.mkRef (#[] : Array (Name × Expr))
    for (n, ci) in env.constants.toList do
      if n.toString.startsWith "_" then continue
      let ty := ci.type
      try
        forallTelescope ty fun xs body => do
          -- require genuinely closed theorem type after telescoping
          unless xs.size == 0 do return ()
          if body.isAppOfArity ``Not 1 then
            negsRef.modify (·.push (n, body.appArg!))
          else
            positivesRef.modify (·.push (n, body))
      catch _ => pure ()
    let positives ← positivesRef.get
    let negs ← negsRef.get
    logInfo m!"closed-like positives {positives.size}, negs {negs.size}"
    let mut count := 0
    for (nn, p) in negs do
      for (pn, q) in positives do
        if (← isDefEq p q) then
          logInfo m!"PAIR neg {nn} pos {pn}\n  {p}"
          count := count + 1
          if count > 100 then return ()
    logInfo m!"pairs {count}"

#scan_contradict_pairs
