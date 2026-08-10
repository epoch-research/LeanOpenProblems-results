import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for n in [``Sat.Valuation.by_cases, ``Sat.Valuation, ``Sat.Literal] do
    logInfo m!"{n}: {env.getModuleIdxFor? n}, {env.find? n |>.map (fun c => c.type)}"
