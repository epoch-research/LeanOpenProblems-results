import FormalConjectures.Util.ProblemImports

open Lean Elab Meta

elab "search_env" : command => do
  let env ← getEnv
  for (name, _) in env.constants do
    let s := name.toString
    if s.contains "conjecture" then
      IO.println s

search_env
