import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
elab "#scanConclPropVarFast" : command => do
  let env ← getEnv
  let mut hits : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if !(ns.startsWith "FormalConjectures" || ns.startsWith "Mathlib" || ns.startsWith "Classical" || ns.startsWith "Exists" || ns.startsWith "False" || ns.startsWith "Not" || ns.startsWith "Iff" || ns.startsWith "Or" || ns.startsWith "And") then continue
    try
      let isHit ← liftTermElabM <| forallTelescopeReducing ci.type fun xs body => do
        let body ← whnf body
        match body with
        | .fvar fid =>
          let ty ← inferType (.fvar fid)
          return ty.isSort && xs.contains (.fvar fid)
        | _ => return false
      if isHit then hits := hits.push n
    catch _ => pure ()
  logInfo m!"hits {hits.size}"
  for n in hits.qsort (fun a b => toString a < toString b) do
    logInfo m!"{n}: {(env.find? n).get!.type}"
#scanConclPropVarFast
