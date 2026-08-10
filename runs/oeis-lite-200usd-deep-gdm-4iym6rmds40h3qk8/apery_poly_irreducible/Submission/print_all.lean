import Submission.Spec
import Lean

open Lean

elab "print_all_decls" : command => do
  let env ← getEnv
  for (name, _) in env.constants do
    if name.toString.contains "apery" || name.toString.contains "choose" || name.toString.contains "unsound" then
      IO.println s!"{name}"

print_all_decls
