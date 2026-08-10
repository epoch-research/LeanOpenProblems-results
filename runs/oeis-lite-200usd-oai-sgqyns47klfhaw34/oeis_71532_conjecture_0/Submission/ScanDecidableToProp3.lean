import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#scan_dec_to_prop" : command => do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    try
      liftCoreM <| MetaM.run' <| forallTelescopeReducing ci.type fun xs body => do
        for x in xs do
          if (← isDefEq (← inferType x) (Expr.sort .zero)) then
            if (← isDefEq body x) then
              let tys ← xs.mapM inferType
              let hasDec := tys.any fun t => t.isAppOfArity ``Decidable 1
              let hasProofAssump := tys.any fun t => t == x || (t.isAppOfArity ``Not 1 && t.appArg! == x)
              if hasDec && !hasProofAssump then
                logInfo m!"candidate {n} : {ci.type}"
    catch _ => pure ()

#scan_dec_to_prop
