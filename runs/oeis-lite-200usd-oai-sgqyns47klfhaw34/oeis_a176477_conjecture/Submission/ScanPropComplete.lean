import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def hasShape (e : Expr) : Bool :=
  match e with
  | .forallE _ (.sort .zero) body _ =>
    -- body mentions bvar 0 inside Nonempty or Decidable or directly
    let rec containsB0 : Expr → Bool
      | .bvar 0 => true
      | .app f a => containsB0 f || containsB0 a
      | .forallE _ t b _ => containsB0 t || containsB0 b
      | .lam _ t b _ => containsB0 t || containsB0 b
      | .mdata _ b => containsB0 b
      | _ => false
    containsB0 body
  | .forallE _ _ b _ => hasShape b
  | _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n,ci) in env.constants.toList do
    if hasShape ci.type then
      let s := toString ci.type
      if s.contains "Nonempty" || s.contains "Decidable" || s.endsWith "α" || s.contains "False" then
        logInfo m!"{n}: {ci.type}"
        c:=c+1
        if c>200 then break
  logInfo m!"c {c}"
