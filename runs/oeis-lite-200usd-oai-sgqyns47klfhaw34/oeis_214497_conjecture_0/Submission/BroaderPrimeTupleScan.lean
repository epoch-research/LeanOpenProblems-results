import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let needles := ["Admiss", "admiss", "Schinzel", "Bunyakov", "Dickson", "Hardy", "Littlewood", "Tuple", "tuple", "Twin", "twin", "primeGap", "PrimeGap", "Polignac", "Constellation", "constellation", "Sophie", "Cunningham"]
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if needles.any (fun s => ns.contains s) then
      logInfo m!"NAME {n} : {ci.type}"
