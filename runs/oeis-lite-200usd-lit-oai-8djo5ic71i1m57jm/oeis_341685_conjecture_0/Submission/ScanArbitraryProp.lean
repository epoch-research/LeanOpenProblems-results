import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def collectForall (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr × Expr) := do
  let e ← whnf e
  match e with
  | .forallE n d b bi =>
      withLocalDecl n bi d fun x => collectForall (b.instantiate1 x) (acc.push x)
  | _ => return (acc, e)

def isLocalProp (locals : Array Expr) (e : Expr) : MetaM Bool := do
  if !e.isFVar then return false
  let t ← inferType e
  let t ← whnf t
  return t.isSort && (← isProp e)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      try
        let (ls, concl) ← liftTermElabM <| collectForall ti.type
        let found ← liftTermElabM <| isLocalProp ls concl
        let foundNot ← liftTermElabM <| match concl with
          | .app (.const ``Not _) p => isLocalProp ls p
          | _ => pure false
        if found || foundNot then
          logInfo m!"CAND {n} : {ti.type}"
          count := count + 1
      catch _ => pure ()
    | _ => pure ()
  logInfo m!"COUNT {count}"
