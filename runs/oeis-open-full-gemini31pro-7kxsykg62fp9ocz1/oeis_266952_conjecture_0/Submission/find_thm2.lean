import FormalConjectures.Util.ProblemImports
import Mathlib

open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.containsSubstr "twin" ∨ s.containsSubstr "Twin" then
      IO.println n
