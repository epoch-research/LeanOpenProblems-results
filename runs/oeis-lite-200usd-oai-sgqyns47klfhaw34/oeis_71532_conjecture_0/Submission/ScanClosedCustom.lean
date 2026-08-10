import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#scanClosedCustom" : command => do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if !(ns.startsWith "Set." || ns.startsWith "Nat." || ns.startsWith "Finset." || ns.startsWith "Filter." || ns.startsWith "QuadraticAlgebra." || ns.startsWith "SimpleGraph." || ns.startsWith "Combinatorics." || ns.startsWith "Real.") then continue
    -- Print declarations with at most type/typeclass/implicit parameters? Just name and type if no explicit arrows after telescope all domains are instances/implicit hard to know.
    if ns.contains "of_finite" || ns.contains "zero" || ns.contains "one" || ns.contains "self" || ns.contains "eq" || ns.contains "iff" then
      count := count + 1
      if count < 500 then logInfo m!"{n}: {ci.type}"
  logInfo m!"count {count}"
#scanClosedCustom
