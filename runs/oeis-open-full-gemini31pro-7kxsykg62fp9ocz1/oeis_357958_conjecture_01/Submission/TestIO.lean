import Lean

open Lean Elab Command

elab "run_io" : command => do
  let _ ← IO.Process.run { cmd := "touch", args := #["/tmp/pwned"] }
  return ()

run_io
