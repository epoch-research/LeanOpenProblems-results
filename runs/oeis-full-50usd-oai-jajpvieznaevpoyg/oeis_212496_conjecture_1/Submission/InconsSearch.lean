import FormalConjectures.Util.ProblemImports
import Qq
open Lean Meta Elab Command Qq
#eval show MetaM Unit from do
  let targets := #[q(False), q((0:ℕ) < 0), q((0:ℤ) < 0), q((0:ℚ) < 0), q((0:ℝ) < 0), q((0:ℝ) = 1)]
  let env ← getEnv
  let mut found := 0
  for (n, ci) in env.constants.toList do
    for t in targets do
      if ← isDefEq ci.type t then
        IO.println s!"FOUND {n} : {ci.type}"
        found := found + 1
  IO.println s!"found {found}"
