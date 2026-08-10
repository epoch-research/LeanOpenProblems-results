import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def allowed (axs : Array Name) : Bool :=
  axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.contains "False" || ns.contains "false" || ns.contains "Proof" || ns.contains "proof" || ns.contains "choice" || ns.contains "complete" || ns == "lcProof" then
      let s := toString ci.type
      if s.contains "False" || s.contains "Prop" || s.contains "Nonempty" || s.contains "α" then
        let axs ← Lean.collectAxioms n
        if allowed axs then
          logInfo m!"ALLOWED {n} : {ci.type}; axioms={axs}"
          c := c+1
        else if ns == "lcProof" || s == "False" || s.contains "∀ {α : Prop}, α" then
          logInfo m!"REJECT {n} : {ci.type}; axioms={axs}"
  logInfo m!"count allowed {c}"
