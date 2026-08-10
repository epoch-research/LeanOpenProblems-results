import FormalConjectures.Util.ProblemImports
-- Try locating the private proof by name search and use impossible-looking specializations.
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.contains "directSumNeZeroMulEquiv._proof" then
      IO.println ns
