import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let targetStx ← [ `(Nonempty PEmpty), `(Inhabited PEmpty), `(Subsingleton Nat), `(1 ≤ (0:Nat)) ]
  let targetExprs ← targetStx.mapM fun stx => Term.elabType stx
  for (n, ci) in env.constants.toList do
    for t in targetExprs do
      let b ← liftTermElabM <| Meta.isDefEq ci.type t
      if b then logInfo m!"bad constant: {n} : {ci.type}"
