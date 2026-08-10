import FormalConjectures.Util.ProblemImports

open Lean Meta

unsafe def arbSortSearch : CoreM Unit := do
  let env ← getEnv
  let mut arb := #[]
  let mut inhab := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    match t with
    | .forallE _ dom body _ =>
      match dom with
      | .sort _ =>
        if body == .bvar 0 then arb := arb.push (n,t)
        if body.isAppOf ``Inhabited then inhab := inhab.push (n,t)
      | _ => pure ()
    | _ => pure ()
  logInfo m!"∀ sort, itself count {arb.size}"
  for (n,t) in arb do logInfo m!"ARBSORT {n}: {t}"
  logInfo m!"∀ sort, Inhabited-ish count {inhab.size}"
  for (n,t) in inhab[:inhab.size.min 100] do logInfo m!"INH {n}: {t}"

#eval! arbSortSearch
