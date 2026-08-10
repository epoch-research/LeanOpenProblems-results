import FormalConjectures.Util.ProblemImports

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let patterns := ["forall (a : Prop), a", "Eq.{1} Nat Nat.zero (Nat.succ Nat.zero)", "Eq.{1} Nat (OfNat.ofNat 0) (OfNat.ofNat 1)"]
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "forall (a : Prop), a" || s.contains "Nat.zero (Nat.succ Nat.zero)" || s.contains "False" then
      if !(s.contains "-> False") && !(s.contains "Not") then
        IO.println s!"{n} : {s}"
