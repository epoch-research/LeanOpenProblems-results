import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
elab "#inspect_not_expr" n:ident : command => do
  liftTermElabM do
    let ci ← getConstInfo n.getId
    forallTelescope ci.type fun xs body => do
      logInfo m!"xs {xs.size} body {body} fn {body.getAppFn} args {body.getAppNumArgs}"
      logInfo m!"isNot {body.isAppOfArity ``Not 1} const? {body.getAppFn.constName?}"
#inspect_not_expr Int.not_odd_zero
#inspect_not_expr ZMod.not_isCyclic_units_eight
