import FormalConjectures.Util.ProblemImports

open Lean Elab Command Meta

elab "#find_forall_prop" : command => do
  let env ← getEnv
  let propSort := mkSort levelZero
  let target1 := mkForall `P BinderInfo.default propSort (mkBVar 0)
  let target2 := mkForall `P BinderInfo.default propSort (mkApp (mkConst ``Not) (mkBVar 0))
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if count < 50 then
      if ci.type == target1 || ci.type == target2 then
        logInfo m!"decl {name} : {ci.type}"
        count := count + 1
  logInfo m!"count={count}"

#find_forall_prop
