import FormalConjectures.Util.ProblemImports
import Mathlib

open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    if n.toString.containsSubstr "266952" then
      IO.println n
