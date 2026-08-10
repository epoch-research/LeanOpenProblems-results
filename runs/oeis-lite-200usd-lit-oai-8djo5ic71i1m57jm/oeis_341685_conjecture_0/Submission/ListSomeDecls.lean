import FormalConjectures.Util.ProblemImports

open Lean Elab Command

elab "#list_some_decls" : command => unsafe do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if c < 50 then
      let ty? := match ci with | .thmInfo ti => some ti.type | .axiomInfo ai => some ai.type | .defnInfo di => some di.type | _ => none
      match ty? with
      | none => pure ()
      | some ty => IO.println s!"{n} | {ty}"; c := c + 1
  IO.println s!"COUNT {c}"

#list_some_decls
