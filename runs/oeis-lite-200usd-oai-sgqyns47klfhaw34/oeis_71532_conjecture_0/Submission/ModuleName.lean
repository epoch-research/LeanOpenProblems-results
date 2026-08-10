import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Sat.Valuation.by_cases | logInfo "none"; return
  logInfo m!"idx={idx}, module={env.header.moduleNames[idx.toNat]!}"
