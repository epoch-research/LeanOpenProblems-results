import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let fmt ← liftTermElabM <| Meta.ppExpr ci.type
    let s := toString fmt
    if s.contains "Nonempty" && (s.contains "∀ {α" || s.contains "∀ (α") then
      let axioms ← Lean.collectAxioms n
      if !(axioms.any (fun a => a == `sorryAx || a == `lcProof)) then
        logInfo m!"{n} : {s} | {axioms.toList}"
        count := count + 1
        if count > 120 then break
  logInfo m!"printed {count}"
