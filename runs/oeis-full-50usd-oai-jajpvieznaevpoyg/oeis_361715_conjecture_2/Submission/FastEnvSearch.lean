import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    unless ci.isUnsafe do
      let ns := n.toString
      if ns.contains "Aper" || ns.contains "ap" || ns.contains "Congr" || ns.contains "ModEq" || ns.contains "Wol" || ns.contains "Jacob" || ns.contains "Lucas" || ns.contains "choose" then
        let s := toString ci.type
        if (s.contains "Nat.Prime" || s.contains "Prime") && (s.contains "ModEq" || s.contains "dvd" || s.contains "∣" || s.contains "choose" || s.contains "factorization") then
          if s.contains "choose" || s.contains "ModEq" || s.contains "pow" || ns.contains "choose" || ns.contains "ModEq" then
            c := c+1
            if c < 300 then logInfo m!"{n} : {ci.type}"
  logInfo m!"COUNT {c}"
