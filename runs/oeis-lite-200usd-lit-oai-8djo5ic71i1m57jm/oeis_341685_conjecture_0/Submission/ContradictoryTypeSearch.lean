import FormalConjectures.Util.ProblemImports
open Lean Meta

partial def hasSuspicious (e : Expr) : Bool :=
  let s := toString e
  (s.contains "False") || (s.contains "Ne" && s.contains "OfNat.ofNat") ||
  (s.contains "Eq" && s.contains "OfNat.ofNat") || (s.contains "Not" && s.contains "True")

#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let safe := match ci with | .axiomInfo ai => !ai.isUnsafe | _ => true
    if safe && hasSuspicious ci.type then
      let ns := toString n
      let ts := toString ci.type
      if (ts.contains "False") || (ts.contains "0") && (ts.contains "Ne" || ts.contains "Not") then
        count := count + 1
        if count < 500 then IO.println s!"{n} : {ci.type}"
  IO.println s!"count {count}"
