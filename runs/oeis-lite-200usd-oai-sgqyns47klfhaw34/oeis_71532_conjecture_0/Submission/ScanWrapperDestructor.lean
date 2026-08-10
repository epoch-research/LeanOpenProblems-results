import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 8000000
open Lean Meta Elab Command

partial def exprHasFVarId (id : Lean.FVarId) : Lean.Expr → Bool
  | .fvar id' => id == id'
  | .app f a => exprHasFVarId id f || exprHasFVarId id a
  | .lam _ t b _ => exprHasFVarId id t || exprHasFVarId id b
  | .forallE _ t b _ => exprHasFVarId id t || exprHasFVarId id b
  | .letE _ t v b _ => exprHasFVarId id t || exprHasFVarId id v || exprHasFVarId id b
  | .mdata _ e => exprHasFVarId id e
  | .proj _ _ e => exprHasFVarId id e
  | _ => false


elab "#scan_wrapper_destructor" : command => do
  liftTermElabM do
    let env ← getEnv
    for (n, ci) in env.constants.toList do
      forallTelescope ci.type fun xs body => do
        -- Look for small declarations returning a type variable α from an argument whose type contains α.
        if xs.size < 1 || xs.size > 5 then return ()
        unless body.isFVar do return ()
        let bd ← body.fvarId!.getDecl
        let bk ← whnf bd.type
        unless bk.isSort do return ()
        for x in xs do
          let xd ← x.fvarId!.getDecl
          if exprHasFVarId body.fvarId! xd.type then
            let ns := n.toString
            unless ns.contains "noConfusion" do
              logInfo m!"DESTRUCTOR? {n}\n  {ci.type}"

#scan_wrapper_destructor
