import FormalConjectures.Util.ProblemImports

open Lean Elab Command

unsafe def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound
unsafe def onlyAllowed (n : Name) : CoreM Bool := do
  let axs ← Lean.collectAxioms n
  pure <| axs.all fun a => allowedAxioms.contains a

elab "#scan_strong" : command => unsafe do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ty? := match ci with | .thmInfo ti => some ti.type | .axiomInfo ai => some ai.type | _ => none
    match ty? with
    | none => pure ()
    | some ty =>
      if c ≤ 2000 && (← liftCoreM <| onlyAllowed n) then
        let s := toString ty
        if (s.contains "Subsingleton" || s.contains "IsEmpty" || s.contains "Finite" || s.contains "Fintype" || s.contains "IsAlgebraic" || s.contains "Transcendental" || s.contains "False" || s.contains "Prime" || s.contains "Squarefree") &&
            (s.contains "Padic" || s.contains "Rat" || s.contains "Nat" || s.contains "False" || s.contains "OfNat") then
          logInfo m!"{n} : {ty}"
          c := c + 1

#scan_strong
