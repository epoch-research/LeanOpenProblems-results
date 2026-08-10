import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#scan_axioms" : command => do
  let env ← getEnv
  let mut count := 0
  let mut total := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .axiomInfo ai =>
      total := total + 1
      let fmt ← liftTermElabM <| ppExpr ai.type
      let s := toString fmt
      if s.contains "False" || s.contains "Sort" || s.contains "Prop" || s.contains "Nonempty" || s.contains "α" then
        logInfo m!"AX {n} : {fmt}"
        count := count + 1
    | .opaqueInfo oi =>
      total := total + 1
      let fmt ← liftTermElabM <| ppExpr oi.type
      let s := toString fmt
      if s.contains "False" || s.contains "Sort" || s.contains "Prop" || s.contains "Nonempty" || s.contains "α" then
        logInfo m!"OP {n} : {fmt}"
        count := count + 1
    | _ => pure ()
  logInfo m!"shown {count}, total axioms/opaques {total}"
#scan_axioms
