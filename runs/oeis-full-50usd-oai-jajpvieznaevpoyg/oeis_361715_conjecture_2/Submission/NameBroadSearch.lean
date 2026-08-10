import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let pats := ["Aper", "Apéry", "apery", "Dwork", "Coster", "Beukers", "Domb", "Almkvist", "Zudilin", "super", "Wolsten", "Ljung", "Jacobsthal", "Kazand", "Granville", "Babbage"]
  let mut c := 0
  for (n, _) in env.constants.toList do
    let s := toString n
    if pats.any (fun pat => s.contains pat) then
      logInfo m!"{n}"
      c := c+1
  logInfo m!"count {c}"
