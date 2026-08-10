import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let t := mkForall `P BinderInfo.default (mkSort levelZero) (mkBVar 0)
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if !(ns.startsWith "AnyPropScan") && !(ns.startsWith "Submission") then
      let ok ← liftTermElabM <| Meta.isDefEq ci.type t
      if ok then
        logInfo m!"ANYPROP {n} : {ci.type}"
        c := c+1
  logInfo m!"count {c}"
