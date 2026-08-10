import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

partial def peelForall : Expr → Expr
| .forallE _ _ b _ => peelForall b
| e => e

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let arr : Array (Name × ConstantInfo) := env.constants.toList.toArray
  let start := 0
  let stop := 2000
  let mut found := 0
  for i in [start:Nat.min stop arr.size] do
    let (name, ci) := arr[i]!
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    try
      let isFalse ← liftTermElabM do
        let r ← whnf (peelForall ci.type)
        return r.isConstOf ``False
      if isFalse then
        let axs ← liftTermElabM <| collectAxioms name
        if axs.all allowedAx then
          logInfo m!"RFALSE {i} {name} : {ci.type} AX {axs.toList}"
          found := found + 1
    catch _ => pure ()
  logInfo m!"found {found} in chunk"
