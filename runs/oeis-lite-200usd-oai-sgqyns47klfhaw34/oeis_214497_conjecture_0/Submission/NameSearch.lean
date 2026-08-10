import FormalConjectures.Util.ProblemImports

open Lean Meta

unsafe def lower (s : String) := s.toLower
unsafe def has (needle hay : String) : Bool := needle.isSubstrOf hay
unsafe def nameSearch : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let s := lower n.toString
    if (has "prime" s) && (has "exists" s || has "gap" s || has "twin" s || has "pair" s || has "consecutive" s || has "constellation" s || has "tuple" s || has "ap" s) then
      arr := arr.push (n, ci.type)
  logInfo m!"matches {arr.size}"
  for (n,t) in arr[:arr.size.min 500] do logInfo m!"MATCH {n}: {t}"

#eval! nameSearch
