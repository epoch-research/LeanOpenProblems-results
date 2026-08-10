import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "#getelem_search" : command => do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let cs := ci.type.getUsedConstants
    if count < 200 && (cs.contains ``GetElem || cs.contains ``GetElem? || cs.contains ``LawfulGetElem) then
      let s := (← liftCoreM <| Meta.MetaM.toIO? sorry) -- dummy
      logWarning m!"{n} : {ci.type}"
      count := count + 1
  logWarning m!"printed {count}"
#getelem_search
