import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def isAllowedAx (n : Name) : Bool := n == `propext || n == `Classical.choice || n == `Quot.sound

-- Find constants with type forall (P : Prop), ... -> P, with no explicit hypothesis exactly P.
#eval show CoreM Unit from do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    let axs ← Lean.collectAxioms n
    if !(axs.all isAllowedAx) then continue
    forallTelescopeReducing ci.type fun xs body => do
      let body ← whnf body
      match body with
      | .fvar fid =>
        let some ldecl := (← getLCtx).find? fid | pure ()
        if (← inferType (.fvar fid)) |>.isSort then
          printed := printed + 1
          if printed < 200 then IO.println s!"{n} : {ci.type}"
      | _ => pure ()
  IO.println s!"printed {printed}"
