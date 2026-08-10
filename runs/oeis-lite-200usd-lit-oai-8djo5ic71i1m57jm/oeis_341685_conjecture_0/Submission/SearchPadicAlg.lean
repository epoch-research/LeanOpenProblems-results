import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    let st := toString ty
    if (st.contains "Padic" || st.contains "ℚ_[") && (st.contains "IsAlgebraic" || st.contains "FiniteDimensional" || st.contains "Module.Finite" || st.contains "FiniteType" || st.contains "minpoly" || st.contains "Algebraic") then
      match ci with
      | .thmInfo _ | .axiomInfo _ | .defnInfo _ | .opaqueInfo _ => logInfo m!"{n} : {ty}"
      | _ => pure ()
