import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    unless ci.isUnsafe do
      let ns := n.toString
      if ns.contains "Aper" || ns.contains "apery" || ns.contains "Congru" || ns.contains "ModEq" || ns.contains "Wolsten" || ns.contains "Jacob" || ns.contains "Lucas" || ns.contains "choose_prime" || ns.contains "prime_pow" || ns.contains "super" then
        c := c+1
        if c < 1000 then logInfo m!"{n}"
  logInfo m!"COUNT {c}"
