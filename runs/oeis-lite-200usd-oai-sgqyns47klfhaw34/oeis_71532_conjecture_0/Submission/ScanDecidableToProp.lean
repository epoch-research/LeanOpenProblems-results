import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (n, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    try
      MetaM.run' do
        forallTelescopeReducing ci.type fun xs body => do
          if body.isAppOfArity ``Not 1 then return ()
          for x in xs do
            if (← isDefEq (← inferType x) (Expr.sort .zero)) then
              if (← isDefEq body x) then
                let tys ← xs.mapM inferType
                let hasDec := tys.any fun t => t.isAppOfArity ``Decidable 1
                if hasDec then
                  logInfo m!"candidate {n} : {ci.type}"
                  found := found + 1
    catch _ => pure ()
  logInfo m!"found {found}"
