import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count > 200 then break
    if n.isInternal then continue
    let s := toString n
    if !(s.startsWith "FormalConjectures" || s.startsWith "Set." || s.startsWith "Nat." || s.startsWith "Real." || s.startsWith "SimpleGraph." || s.startsWith "EuclideanGeometry." || s.startsWith "Algebra." || s.startsWith "Is" || s.startsWith "Polynomial." || s.startsWith "Finset." || s.startsWith "Filter." || s.startsWith "lcProof") then
      continue
    let axioms ← Lean.collectAxioms n
    if axioms.any (fun a => a == `sorryAx || a == `lcProof) then
      logInfo m!"{n} axioms {axioms.toList}"
      count := count + 1
  logInfo m!"printed {count}"
