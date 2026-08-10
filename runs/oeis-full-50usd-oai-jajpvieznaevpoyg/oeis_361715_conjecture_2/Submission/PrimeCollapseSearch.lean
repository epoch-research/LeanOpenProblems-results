import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut nfound := 0
  for (n, ci) in env.constants.toList do
    unless ci.isUnsafe do
      let s := toString ci.type
      if (s.contains "Nat.Prime" && (s.contains "≤ 3" || s.contains "< 5" || s.contains "¬5 ≤" || s.contains "p < 5" || s.contains "p ≤ 3")) then
        nfound := nfound + 1
        if nfound < 100 then logInfo m!"{n} : {ci.type}"
  logInfo m!"found {nfound}"
