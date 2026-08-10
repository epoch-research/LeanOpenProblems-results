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
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    let synt := peelForall ci.type
    -- cheap string/name prefilter: either syntactically false-ish or result is an app/const, reduce only limited by try
    try
      let isFalse ← liftTermElabM do
        let r ← whnf synt
        return r.isConstOf ``False
      if isFalse then
        let axs ← liftTermElabM <| collectAxioms name
        if axs.all allowedAx then
          if found < 300 then logInfo m!"RFALSE {name} : {ci.type} AX {axs.toList}"
          found := found + 1
    catch _ => pure ()
  logInfo m!"found {found}"
