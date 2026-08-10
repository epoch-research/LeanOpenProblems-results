import FormalConjectures.Util.ProblemImports

open Lean Meta

#elab "find_gamma_lemmas" : tactic => do
  let env ← getEnv
  for (name, _) in env.constants do
    if name.toString.contains "Gamma" && (name.toString.contains "Real" || name.toString.contains "Complex") then
      IO.println name.toString

example : True := by
  find_gamma_lemmas
  trivial
