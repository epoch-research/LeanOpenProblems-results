import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def hasLooseBVar0 : Expr → Bool
| .bvar 0 => true
| .app f a => hasLooseBVar0 f || hasLooseBVar0 a
| .lam _ t b _ => hasLooseBVar0 t || hasLooseBVar0 b
| .forallE _ t b _ => hasLooseBVar0 t || hasLooseBVar0 b
| .letE _ t v b _ => hasLooseBVar0 t || hasLooseBVar0 v || hasLooseBVar0 b
| .mdata _ e => hasLooseBVar0 e
| .proj _ _ e => hasLooseBVar0 e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let propSort := Expr.sort .zero
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let t := ci.type.consumeMData
    match t with
    | .forallE _ dom body _ =>
      if dom.consumeMData == propSort then
        let body := body.consumeMData
        -- after binding P, body is bvar 0 or forall ending in bvar maybe
        if body == .bvar 0 || hasLooseBVar0 body then
          let s := toString (← liftTermElabM <| ppExpr t)
          if s.contains "∀ (P : Prop), P" || s.contains "∀ (p : Prop), p" || s.contains "Prop)" then
            logInfo m!"{n} : {s}"
            c:=c+1
            if c>100 then break
    | _ => pure ()
  logInfo m!"count {c}"
