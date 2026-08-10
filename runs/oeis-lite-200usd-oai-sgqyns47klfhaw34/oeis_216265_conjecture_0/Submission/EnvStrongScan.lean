import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    let s := toString t
    if (s.contains "Nat.Prime" || s.contains "Nat.primeCounting" || s.contains "Nat.nth" || s.contains "primeGap" || s.contains "π") &&
       (s.contains "Eventually" || s.contains "∀ᶠ" || s.contains "IsBigO" || s.contains "=O" || s.contains "≤" || s.contains "<" || s.contains "Tendsto" || s.contains "atTop") then
      if !(toString n).contains "EnvStrongScan" then
        logInfo m!"{n} : {t}"
        c := c + 1
        if c > 500 then break
  logInfo m!"count shown {c}"
