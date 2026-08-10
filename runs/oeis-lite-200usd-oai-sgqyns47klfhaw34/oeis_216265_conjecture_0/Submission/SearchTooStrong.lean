import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def exprHasForallPropToSelf (e : Expr) : Bool :=
  false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    -- Print declarations whose type syntactically is forall P : Prop, P or forall a, False-like after one binder.
    match t with
    | .forallE _ dom body _ =>
      if dom.isSort && (dom.sortLevel! == 0) then
        let b := body.instantiate1 (.bvar 0)
        if b == .bvar 0 then
          logInfo m!"forall_prop_self? {n} : {t}"
          found := found + 1
        if b.isConstOf ``False then
          logInfo m!"forall_prop_false? {n} : {t}"
          found := found + 1
    | _ => pure ()
  logInfo m!"found {found}"
