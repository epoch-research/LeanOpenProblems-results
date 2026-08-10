import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#closed_false_decls" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut names : Array Name := #[]
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let ty ← whnf ci.type
      if ty.isConstOf ``False then
        names := names.push name
    logInfo m!"{names}"

#closed_false_decls
