import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def allowed (axs : Array Name) : Bool :=
  axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let anyPropType := mkForall `P BinderInfo.default (mkSort levelZero) (mkBVar 0)
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if !(ns.startsWith "SuspiciousAllowedScan") && !(ns.startsWith "Submission") then
      let s := toString ci.type
      let suspicious := s == "False" || s.contains "∀ {α : Prop}, α" || s.contains "∀ (α : Prop), α" || s.contains "Nonempty False" || ns == "lcProof"
      if suspicious then
        let axs ← Lean.collectAxioms n
        if allowed axs then
          logInfo m!"ALLOWED SUSP {n} : {ci.type}; axioms={axs}"
          c := c+1
        else
          logInfo m!"REJECT SUSP {n} : {ci.type}; axioms={axs}"
  logInfo m!"count allowed {c}"
