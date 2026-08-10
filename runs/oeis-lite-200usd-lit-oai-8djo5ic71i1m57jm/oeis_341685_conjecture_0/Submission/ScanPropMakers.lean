import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 1000000
open Lean Meta Elab Command
unsafe def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound
elab "#scan_prop_makers" : command => unsafe do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if !n.isInternal then
      let axs ← liftCoreM <| Lean.collectAxioms n
      if axs.all (fun a => allowedAxioms.contains a) then
        let s := toString ci.type
        if (s.contains "Sort.zero" || s.contains "Prop") &&
           (s.contains "Nonempty" || s.contains "Inhabited" || s.contains "Decidable" || s.contains "forall" || s.contains "Not" || s.contains "False") then
          if s.contains "Expr.sort" || s.contains "Prop" || s.contains "False" then
            IO.println s!"{n} : {ci.type}"
#scan_prop_makers
