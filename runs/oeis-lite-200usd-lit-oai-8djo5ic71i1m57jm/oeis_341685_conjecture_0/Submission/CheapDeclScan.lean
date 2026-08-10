import FormalConjectures.Util.ProblemImports
open Lean Meta

set_option maxHeartbeats 800000

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `FormalConjectures.Util.ProblemImports}] {} 0
  let keys := ["IsAlgebraic", "Transcendental", "Padic", "padic", "Module.Finite", "FiniteDimensional", "NumberField", "IsQuadraticExtension", "IsField", "algebraicClosure", "not_isAlgebraic", "isAlgebraic", "false", "False"]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    let ts := toString ci.type
    if keys.any (fun k => ns.contains k || ts.contains k) then
      if ts.length < 2000 then
        IO.println s!"{n} : {ci.type}"
        count := count + 1
        if count > 2000 then break
  IO.eprintln s!"printed {count}"
#eval main
