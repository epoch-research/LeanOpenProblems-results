import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let patterns := ["∀ {α : Prop}, α", "∀ (α : Prop), α", "∀ {P : Prop}, P", "∀ (P : Prop), P", "False", "Nonempty False"]
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    let s := toString ci.type
    if patterns.any (fun pat => s.contains pat) then
      if !(ns.startsWith "ArbitraryPropTypeScan") && !(ns.startsWith "Submission") then
        logInfo m!"{n} : {ci.type}"
        c := c+1
        if c > 200 then break
  logInfo m!"count {c}"
