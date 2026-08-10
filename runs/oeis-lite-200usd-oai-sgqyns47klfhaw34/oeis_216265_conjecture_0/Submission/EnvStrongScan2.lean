import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let prefixes := ["Nat.", "Chebyshev.", "Asymptotics.", "prime", "Prime", "FormalConjectures"]
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if prefixes.any (fun p => ns.startsWith p) then
      let s := toString ci.type
      if (s.contains "Nat.Prime" || s.contains "primeCounting" || s.contains "nth" || s.contains "primeGap" || s.contains "Chebyshev") &&
         (s.contains "Eventually" || s.contains "∀ᶠ" || s.contains "IsBigO" || s.contains "≤" || s.contains "<" || s.contains "Tendsto" || s.contains "atTop") then
        logInfo m!"{n} : {ci.type}"
        c := c + 1
        if c > 400 then break
  logInfo m!"count shown {c}"
