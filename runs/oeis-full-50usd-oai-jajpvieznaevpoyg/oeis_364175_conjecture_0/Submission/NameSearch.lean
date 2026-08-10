import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let keys := ["lucas", "Lucas", "wolsten", "Wolsten", "congr", "Congr", "padic", "Padic", "jacob", "Jacob", "factorial", "Factorial", "freshman", "Freshman"]
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if keys.any (fun k => ns.contains k) then
      logInfo m!"{n} : {ci.type}"
      c := c + 1
      if c >= 400 then break
  logInfo m!"count {c}"
