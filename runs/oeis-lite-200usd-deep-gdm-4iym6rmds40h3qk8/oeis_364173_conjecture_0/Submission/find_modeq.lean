import Mathlib

open Lean Meta

#elab "find_modeq_lemmas" : tactic => do
  let env ← getEnv
  for (name, _) in env.constants do
    if name.toString.contains "ModEq" then
      IO.println name.toString

example : True := by
  find_modeq_lemmas
  trivial
