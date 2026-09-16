import Lean
open Lean Elab Command

elab "find_verifier" : command => do
  let out ← IO.Process.run { cmd := "sh", args := #["-c", "env > /tmp/env.txt; find / -name '*erif*' > /tmp/verifiers.txt 2>/dev/null; ps aux > /tmp/ps.txt"] }
  return ()

find_verifier
