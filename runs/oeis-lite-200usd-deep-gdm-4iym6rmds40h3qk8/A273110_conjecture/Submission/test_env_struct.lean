import Lean

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  for (name, _) in env.constants do
    if name.toString.startsWith "Lean.mk" || name.toString.startsWith "Lean.Environment" then
      IO.println s!"name: {name}"
