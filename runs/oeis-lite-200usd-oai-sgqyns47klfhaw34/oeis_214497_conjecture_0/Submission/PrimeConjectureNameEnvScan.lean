import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let needles := ["twin", "Twin", "gap", "Gap", "constellation", "Constellation", "tuple", "Tuple", "Dickson", "Schinzel", "Bunyakovsky", "Hardy", "Littlewood", "Goldbach", "Polignac", "primeGap", "PrimeGap"]
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes then continue
    let ns := toString name
    if needles.any (fun x => ns.contains x) then
      logInfo m!"PNAME {name} unsafe={ci.isUnsafe} : {ci.type}"
      found := found + 1
      if found > 500 then break
  logInfo m!"found {found}"
