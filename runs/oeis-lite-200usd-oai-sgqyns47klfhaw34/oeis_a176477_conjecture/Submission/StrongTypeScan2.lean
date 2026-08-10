import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    let suspicious :=
      (s.contains "∀ (P : Prop), P") ||
      ((s.contains "∀ (α : Sort") && (s.contains "Nonempty α")) ||
      (s.contains "∀ (a b : ℕ), a = b") ||
      (s.contains "∀ (n : ℕ), n = 0") ||
      (s == "False") || (s == "Nonempty False") ||
      (s.contains "0 = 1") || (s.contains "1 = 0")
    if suspicious then
      IO.println s!"{n} : {s}"
      count := count + 1
      if count > 200 then break
  IO.println s!"count {count}"
