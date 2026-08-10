import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target := mkForall `P BinderInfo.default (mkSort levelZero) (mkBVar 0)
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if count < 20 then
      let ok ← liftTermElabM <| isDefEq ci.type target
      if ok then
        let axs ← collectAxioms name
        logInfo m!"{name} : {ci.type}; axioms={axs.toList}"
        count := count + 1
