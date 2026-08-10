import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#prime_add_sub_names" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut out : Array Name := #[]
    for (name, ci) in env.constants.toList do
      let ns := toString name
      if (ns.contains "Prime" || ns.contains "prime") && (ns.contains "add" || ns.contains "sub" || ns.contains "succ" || ns.contains "pred" || ns.contains "two" || ns.contains "eq") then
        out := out.push name
    for n in out.qsort (fun a b => toString a < toString b) do
      logInfo m!"{n}"

#prime_add_sub_names
