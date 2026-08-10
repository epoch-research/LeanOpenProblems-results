import Mathlib

open Lean Meta

#elab "print_all_axioms" : tactic => do
  let env ← getEnv
  for (name, constInfo) in env.constants do
    if constInfo.isAxiom then
      IO.println s!"Axiom: {name}"

example : True := by
  print_all_axioms
  trivial
