import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def isAllowedAx (n : Name) : Bool := n == `propext || n == `Classical.choice || n == `Quot.sound

partial def headName? (e : Expr) : Option Name :=
  if e.isApp then headName? e.getAppFn else match e with | .const n _ => some n | _ => none

#eval show CoreM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type.consumeMData
    -- print closed props with name containing false/contrad/not_ne maybe
    if (toString n).contains "false" || (toString n).contains "False" || (toString n).contains "contrad" then
      let axs := (collectAxioms env n).run' { recursive := true }
      if axs.all isAllowedAx then
        c := c + 1
        if c < 300 then IO.println s!"{n} : {ty}"
  IO.println s!"candidates={c}"
