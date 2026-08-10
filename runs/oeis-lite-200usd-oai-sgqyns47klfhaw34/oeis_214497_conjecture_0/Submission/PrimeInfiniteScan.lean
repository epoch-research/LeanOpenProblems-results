import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

partial def containsConstName (needle : Name) : Expr → Bool
| .const n _ => n == needle
| .app f a => containsConstName needle f || containsConstName needle a
| .lam _ t b _ => containsConstName needle t || containsConstName needle b
| .forallE _ t b _ => containsConstName needle t || containsConstName needle b
| .letE _ t v b _ => containsConstName needle t || containsConstName needle v || containsConstName needle b
| .mdata _ b => containsConstName needle b
| .proj _ _ b => containsConstName needle b
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    if containsConstName ``Nat.Prime ci.type && (containsConstName ``Set.Infinite ci.type || containsConstName ``Infinite ci.type) then
      let axs ← liftTermElabM <| collectAxioms name
      if axs.all allowedAx then
        logInfo m!"PINF {name} : {ci.type} AX {axs.toList}"
        found := found + 1
        if found > 300 then break
  logInfo m!"found {found}"
