import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta

def searchEnv : MetaM Unit := do
  let env ← getEnv
  let mut found := []
  for (name, _) in env.constants do
    let n_str := name.toString
    if n_str.toLower.contains "wolstenholme" then
      found := name :: found
  IO.println s!"Found {found.length} matches."
  for name in found do
    IO.println s!"- {name}"

#eval! searchEnv











