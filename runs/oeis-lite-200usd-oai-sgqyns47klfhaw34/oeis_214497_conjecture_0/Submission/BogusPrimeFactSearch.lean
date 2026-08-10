import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

partial def finalResult : Expr → Expr
| .forallE _ _ b _ => finalResult b
| e => e

def isNatPrimeLit (k : Nat) (e : Expr) : Bool :=
  e.isAppOfArity ``Nat.Prime 1 && e.getArg! 0 == mkNatLit k

#eval show CommandElabM Unit from do
  let env ← getEnv
  for k in [0,1,4,6,8,9,10,12,15,21] do
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      if isNatPrimeLit k (finalResult ci.type) then
        let ax ← collectAxioms name
        if ax.all allowedAx then
          logInfo m!"Nat.Prime {k}: {name} : {ci.type} AX {ax.toList}"
          shown := shown + 1
    logInfo m!"k={k} shown={shown}"
