import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

partial def resultExpr : Expr → Expr
| .forallE _ _ b _ => resultExpr b
| e => e

partial def isBVarResult : Expr → Bool
| .bvar _ => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    if isBVarResult (resultExpr ci.type) then
      let s := toString ci.type
      if s.contains "Prop" then
        let axs ← liftTermElabM <| collectAxioms name
        if axs.all allowedAx then
          logInfo m!"ARBRES {name} : {ci.type} AX {axs.toList}"
          found := found + 1
          if found > 300 then break
  logInfo m!"found {found}"
