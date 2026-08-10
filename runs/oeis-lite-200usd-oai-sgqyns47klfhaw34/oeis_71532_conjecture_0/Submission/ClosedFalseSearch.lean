import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term

partial def finalIsFalse : Expr → Bool
| .forallE _ _ b _ => finalIsFalse b
| .mdata _ e => finalIsFalse e
| .const ``False _ => true
| _ => false

elab "#closed_false_search" : command => do
  let env ← getEnv
  let ref ← IO.mkRef 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    if !finalIsFalse ci.type then continue
    if name == `lcProof then continue
    try
      liftTermElabM do
        let us := ci.levelParams.map Level.param
        let c := Lean.mkConst name us
        forallTelescopeReducing ci.type fun xs body => do
          unless body == Lean.mkConst ``False do return ()
          synthesizeSyntheticMVarsNoPostponing
          let expr ← instantiateMVars (mkAppN c xs)
          let ty ← inferType expr >>= instantiateMVars
          if ty == Lean.mkConst ``False && !expr.hasExprMVar then
            let n ← ref.get
            if n < 50 then
              let axs ← Lean.collectAxioms name
              logInfo m!"closed? {name} : {ci.type} axs={axs} term={expr}"
            ref.set (n+1)
    catch _ => pure ()
  logInfo m!"shown {(← ref.get)}"

#closed_false_search
