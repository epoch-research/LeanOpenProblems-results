import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.startsWith "FormalConjectures" || s.startsWith "Nat." || s.startsWith "SimpleGraph." || s.startsWith "Set." || s.startsWith "Has" || s.startsWith "Is" || s.startsWith "Algebra." || s.startsWith "EuclideanGeometry." then
      let axs ← Lean.collectAxioms n
      if axs.any (fun a => a == `sorryAx || a == `lcProof) then
        count := count + 1
        logInfo m!"BADAX {n}: {axs.toList} : {ci.type}"
  logInfo m!"count {count}"
