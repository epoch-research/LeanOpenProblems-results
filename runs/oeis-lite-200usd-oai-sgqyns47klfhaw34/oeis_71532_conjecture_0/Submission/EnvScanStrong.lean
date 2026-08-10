import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let s := toString (← liftTermElabM <| ppExpr ci.type)
    if (s.contains "False" || s.contains "Empty" || s.contains "PEmpty" || s.contains "Nonempty" || s.contains "∀ (P : Prop), P" || s.contains "Prop →") then
      -- print suspicious closed false-ish things, not constructors/ind recursors too much
      if s == "False" || s.contains "Nonempty Empty" || s.contains "Nonempty PEmpty" || s.contains "Inhabited False" || s.contains "Inhabited Empty" || s.contains "∀ (P : Prop), P" then
        logInfo m!"{n} : {s}"
        count := count + 1
  logInfo m!"count={count}"
