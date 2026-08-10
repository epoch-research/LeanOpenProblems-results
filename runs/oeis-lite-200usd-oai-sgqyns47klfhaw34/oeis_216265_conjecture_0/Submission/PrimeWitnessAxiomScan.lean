import FormalConjectures.Util.ProblemImports
open Lean Elab Command

def allowed (axs : Array Name) : Bool :=
  axs.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.startsWith "Nat." || ns.startsWith "Chebyshev." || ns.contains "prime" || ns.contains "Prime" || ns.contains "Bertrand" then
      let s := toString ci.type
      if (s.contains "∃" && (s.contains "Nat.Prime" || s.contains ".Prime")) && (s.contains "≤" || s.contains "<" || s.contains ">") then
        let axs ← Lean.collectAxioms n
        if allowed axs then
          logInfo m!"ALLOWED {n} : {ci.type}"
          c := c+1
          if c > 200 then break
  logInfo m!"count {c}"
