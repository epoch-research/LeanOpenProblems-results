import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed (axs : Array Name) : Bool :=
    axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
  let P := Expr.bvar 1
  let Q := Expr.bvar 0
  for (name, ci) in env.constants.toList do
    let axs ← collectAxioms name
    if allowed axs then
      match ci.type with
      | .forallE _ d1 b1 _ =>
        if d1 == .sort .zero then
          let body1 := b1
          -- ∀ P : Prop, P
          if body1 == .bvar 0 then logInfo m!"ALLPROP {name} : {ci.type}"
          match body1 with
          | .forallE _ d2 b2 _ =>
            if d2 == .sort .zero then
              match b2 with
              | .forallE _ d3 b3 _ =>
                -- ∀ P Q, P -> Q has d3 = bvar 1, body bvar 1? (under binder, Q is bvar1, P bvar2)
                if d3 == .bvar 1 && b3 == .bvar 1 then
                  logInfo m!"IMPANY {name} : {ci.type}"
              | _ => pure ()
          | _ => pure ()
      | _ => pure ()
  logInfo "done"
