import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def allPropProofLike : Expr → Bool
| .forallE _ d b _ => d.isSort && allPropProofLike b
| .bvar 0 => true
| _ => false
#eval! show CommandElabM Unit from liftTermElabM <| MetaM.run' do
  let env ← getEnv
  let mut cf := 0
  let mut ca := 0
  for (n, ci) in env.constants.toList do
    let t ← whnf ci.type
    if t.isConstOf ``False then
      logInfo m!"False-like {n} : {ci.type}"
      cf := cf+1
    if ca < 20 && allPropProofLike t && n != `lcProof && n != `lcUnreachable then
      logInfo m!"all-like {n} : {ci.type}"
      ca := ca+1
  logInfo m!"counts false {cf} all {ca}"
