import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def hasNamePart (parts : List String) : Expr → Bool
| .const n _ => parts.any (fun s => n.toString.contains s)
| .app f a => hasNamePart parts f || hasNamePart parts a
| .lam _ t b _ => hasNamePart parts t || hasNamePart parts b
| .forallE _ t b _ => hasNamePart parts t || hasNamePart parts b
| .letE _ t v b _ => hasNamePart parts t || hasNamePart parts v || hasNamePart parts b
| .mdata _ b => hasNamePart parts b
| .proj _ _ b => hasNamePart parts b
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let parts := ["False", "Nat.Prime", "primeCounting", "Nat.count", "forall_exists_prime"]
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if !ns.startsWith "Lean" && !ns.startsWith "Mathlib.Tactic" && hasNamePart parts ci.type then
      let s := toString ci.type
      if s.contains "False" || s.contains "primeCounting" || s.contains "Nat.Prime" then
        arr := arr.push (ns ++ " : " ++ s)
  arr := arr.qsort (fun a b => a < b)
  for s in arr[:min arr.size 600] do IO.println s
