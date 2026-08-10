import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let pats := #["Aper", "apery", "Dwork", "Coster", "Beukers", "Domb", "Almkvist", "Zudilin", "super", "Wolsten", "Ljung", "Jacobsthal", "Kazand", "Granville", "Babbage"]
  let mut arr := #[]
  for (n, _) in env.constants.toList do
    let s := toString n
    if pats.any (fun pat => s.contains pat) then
      arr := arr.push n
  for n in arr[:min arr.size 200] do logInfo m!"{n}"
  logInfo m!"count {arr.size}"
