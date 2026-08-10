import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let needles := ["0 = 1", "1 = 0", "Nat.succ", "OfNat.ofNat"]
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "0 = 1" || s.contains "1 = 0") then
      if shown < 100 then logInfo m!"{name} : {ci.type}"
      shown := shown + 1
  logInfo m!"shown/count {shown}"
