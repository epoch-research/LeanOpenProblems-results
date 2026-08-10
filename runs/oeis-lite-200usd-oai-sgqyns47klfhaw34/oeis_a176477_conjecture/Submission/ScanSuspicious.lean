import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type.cleanupAnnotations
    -- Print names containing obvious theorem/proof/hack/lc/unsafe or returning Prop variable directly.
    if n.toString.contains "lc" || n.toString.contains "proof" || n.toString.contains "Proof" || n.toString.contains "unsafe" then
      match ci with
      | .axiomInfo _ => logInfo m!"axiom-ish {n} : {ty}"; c := c+1
      | .opaqueInfo _ => logInfo m!"opaque-ish {n} : {ty}"; c := c+1
      | _ => pure ()
  logInfo m!"count {c}"
