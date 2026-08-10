import FormalConjectures.Util.ProblemImports

open Lean Elab Command

unsafe def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

elab "#list_fc_decls" : command => unsafe do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if ns.startsWith "FormalConjecturesForMathlib" || ns.startsWith "Nat." || ns.startsWith "SimpleGraph." || ns.startsWith "Polynomial." || ns.startsWith "Set." || ns.startsWith "Real." || ns.startsWith "Finset." || ns.startsWith "Additively" || ns.startsWith "Is" then
      let ty? := match ci with | .thmInfo ti => some ti.type | .axiomInfo ai => some ai.type | .defnInfo di => if ns.startsWith "FormalConjecturesForMathlib" then some di.type else none | _ => none
      match ty? with
      | none => pure ()
      | some ty =>
        let axs ← liftCoreM <| Lean.collectAxioms n
        let bad := axs.any (fun a => !(allowedAxioms.contains a))
        IO.println s!"{n} | bad={bad} | {ty}"

#list_fc_decls
