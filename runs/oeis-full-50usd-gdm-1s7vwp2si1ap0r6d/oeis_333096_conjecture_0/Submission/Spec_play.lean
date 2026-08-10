import FormalConjectures.Util.ProblemImports

open Lean Elab Command

run_cmd do
  let out ← IO.Process.output { cmd := "ls", args := #["-la", "/workspace"] }
  logInfo s!"Output of ls: {out.stdout}"
