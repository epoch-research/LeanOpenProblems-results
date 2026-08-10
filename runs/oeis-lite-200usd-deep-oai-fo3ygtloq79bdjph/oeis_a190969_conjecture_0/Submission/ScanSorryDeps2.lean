import FormalConjectures.Util.ProblemImports

open Lean
partial def hasConstName (nm : Name) : Expr → Bool
| .const n _ => n == nm
| .app f a => hasConstName nm f || hasConstName nm a
| .lam _ t b _ => hasConstName nm t || hasConstName nm b
| .forallE _ t b _ => hasConstName nm t || hasConstName nm b
| .letE _ t v b _ => hasConstName nm t || hasConstName nm v || hasConstName nm b
| .mdata _ e => hasConstName nm e
| .proj _ _ e => hasConstName nm e
| _ => false

#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci.value? with
    | some v =>
      if hasConstName ``sorryAx v then
        IO.println s!"{n} : {ci.type}"
        count := count + 1
        if count > 300 then break
    | none => pure ()
  IO.println s!"count shown {count}"
