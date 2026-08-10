import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if !(ns.startsWith "PrimeWitnessTypeScan") && !(ns.startsWith "Submission") then
      let s := toString ci.type
      -- Print constants returning an existential Nat.Prime and containing at least one inequality.
      if (s.contains "∃" && s.contains "Nat.Prime") && (s.contains "≤" || s.contains "<" || s.contains ">") then
        if !(s.contains "Ideal") && !(s.contains "PrimeSpectrum") && !(s.contains "ZMod p") then
          logInfo m!"{n} : {ci.type}"
          c := c+1
          if c > 500 then break
  logInfo m!"count {c}"
