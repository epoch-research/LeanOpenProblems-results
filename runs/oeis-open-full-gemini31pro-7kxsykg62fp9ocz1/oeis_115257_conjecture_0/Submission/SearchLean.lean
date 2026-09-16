import Mathlib
import FormalConjecturesForMathlib

open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  for (n, _) in env.constants do
    if n.toString.containsSubstr "115257" then
      IO.println n
