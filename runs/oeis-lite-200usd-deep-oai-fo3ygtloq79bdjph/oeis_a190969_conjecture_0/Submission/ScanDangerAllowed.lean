import FormalConjectures.Util.ProblemImports
open Lean Meta
partial def hasConstName (n : Name) : Expr → Bool
| .const m _ => m == n
| .app f a => hasConstName n f || hasConstName n a
| .lam _ t b _ => hasConstName n t || hasConstName n b
| .forallE _ t b _ => hasConstName n t || hasConstName n b
| .letE _ t v b _ => hasConstName n t || hasConstName n v || hasConstName n b
| .mdata _ e => hasConstName n e
| .proj _ _ e => hasConstName n e
| _ => false
#eval show CoreM Unit from do
  let allowedList := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in (← getEnv).constants.toList do
    if n.isInternal then continue
    let ty := ci.type
    let tys := toString ty
    if (hasConstName ``False ty) || (tys.contains "∀ (P : Prop), P") || (tys.contains "Nonempty False") then
      let ax ← collectAxioms n
      if ax.all (fun a => allowedList.contains a) then
        IO.println s!"{n} : {ty} AX {ax}"
        count := count+1
        if count > 200 then break
  IO.println s!"count {count}"
