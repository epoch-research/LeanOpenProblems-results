import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def final : Expr → Expr
| .forallE _ _ b _ => final b
| .mdata _ e => final e
| e => e

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c:=0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let r := final ci.type.consumeMData
    match r with
    | .bvar i =>
      let s := toString (← liftTermElabM <| ppExpr ci.type)
      if s.contains ": Prop" then
        logInfo m!"{n} : {s}"
        c:=c+1
        if c>300 then break
    | _ => pure ()
  logInfo m!"count={c}"
