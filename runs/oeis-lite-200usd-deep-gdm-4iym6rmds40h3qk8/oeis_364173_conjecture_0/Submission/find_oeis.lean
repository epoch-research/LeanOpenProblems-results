import FormalConjectures.Util.ProblemImports

open Lean Meta

elab "find_oeis" : tactic => do
  let env ← getEnv
  for (name, _) in env.constants do
    if name.toString.contains "oeis" || name.toString.contains "OEIS" then
      IO.println name.toString

example : True := by
  find_oeis
  trivial
