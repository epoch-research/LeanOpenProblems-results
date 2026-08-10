import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def isAllowedAx (n : Name) : Bool := n == `propext || n == `Classical.choice || n == `Quot.sound

#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    if ty.isConstOf ``False then
      let axs := (collectAxioms env n).run' { recursive := true }
      if axs.all isAllowedAx then
        count := count + 1
        IO.println s!"{n} : {ty} axioms={axs}"
  IO.println s!"count={count}"
