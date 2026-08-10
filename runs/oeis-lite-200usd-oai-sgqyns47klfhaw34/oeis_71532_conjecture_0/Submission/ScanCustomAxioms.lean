import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta

#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  let mut sor := 0
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.startsWith "FormalConjecturesForMathlib" || s.startsWith "Nat." || s.startsWith "Set." || s.startsWith "Finset." || s.startsWith "Combinatorics." || s.startsWith "SimpleGraph." || s.startsWith "Real." || s.startsWith "QuadraticAlgebra." || s.startsWith "Filter." then
      -- too broad includes mathlib Nat; filter custom names by substring list impossible. Just collect if type string contains custom defs?
      if (s.contains "hasDensity" || s.contains "IsAsymptotic" || s.contains "hypergraphRamsey" || s.contains "squarefreePart" || s.contains "maxPrimeFac" || s.contains "Full" || s.contains "IsPerfectPower" || s.contains "iteratedLog") then
        count := count + 1
        let axs ← Lean.collectAxioms n
        if axs.contains `sorryAx then
          sor := sor + 1; IO.println s!"sorry {n} : {ci.type}"
        else IO.println s!"ok {n} axs={axs}"
  IO.println s!"count={count} sor={sor}"
