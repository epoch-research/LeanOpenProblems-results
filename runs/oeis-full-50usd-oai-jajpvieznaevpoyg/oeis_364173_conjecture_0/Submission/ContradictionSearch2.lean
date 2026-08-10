import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst
  let mut count : Nat := 0
  for n in names do
    let ci := env.find? n |>.get!
    let s := toString ci.type
    if s == "False" || s.contains "Subsingleton ℤ" || s.contains "Subsingleton Int" ||
       s.contains "∀ (a b : ℤ), a = b" || s.contains "∀ (a b : Int), a = b" ||
       s.contains "∀ (n a b : ℤ), a ≡ b" || s.contains "∀ (n a b : Int)," then
      if count < (200 : Nat) then logInfo m!"{n} : {ci.type}"
      count := count + 1
  logInfo m!"count={count}"
