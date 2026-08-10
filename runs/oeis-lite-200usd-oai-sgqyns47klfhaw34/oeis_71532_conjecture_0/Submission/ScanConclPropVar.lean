import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def allowed (axs : Array Name) : Bool := axs.all fun n => n == `propext || n == `Classical.choice || n == `Quot.sound

elab "#scanConclPropVar" : command => do
  let env ← getEnv
  let mut hits : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (toString n).startsWith "_private" then continue
    try
      let isHit ← liftTermElabM <| forallTelescopeReducing ci.type fun xs body => do
        let body ← whnf body
        match body with
        | .fvar fid =>
          let ty ← inferType (.fvar fid)
          return ty.isSort && xs.contains (.fvar fid)
        | _ => return false
      if isHit then
        let axs ← liftCoreM <| Lean.collectAxioms n
        if allowed axs then hits := hits.push n
    catch _ => pure ()
  logInfo m!"hits {hits.size}"
  for n in hits.qsort (fun a b => toString a < toString b) do
    logInfo m!"{n}: {(env.find? n).get!.type}"

#scanConclPropVar
