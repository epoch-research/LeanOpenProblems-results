import Submission.Spec

open Lean Elab Command

run_meta do
  let env ← getEnv
  if env.contains `A308734_eq then
    IO.println "A308734_eq IS in the imported environment!"
  else
    IO.println "A308734_eq is NOT in the imported environment!"
