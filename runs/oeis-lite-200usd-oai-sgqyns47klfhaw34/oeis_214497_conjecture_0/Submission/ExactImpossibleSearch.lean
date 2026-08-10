import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

def isExactSuspicious (e : Expr) : Bool :=
  e.isConstOf ``False ||
  (e.isAppOfArity ``Eq 3 && e.getArg! 1 == mkNatLit 0 && e.getArg! 2 == mkNatLit 1) ||
  (e.isAppOfArity ``Eq 3 && e.getArg! 1 == mkNatLit 1 && e.getArg! 2 == mkNatLit 0)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    if isExactSuspicious ci.type then
      let ax ← MetaM.toIO (collectAxioms name) {} { env := env } |>.toBaseIO
      if ax.all allowedAx then
        count := count + 1
        logInfo m!"{name} : {ci.type} AX {ax.toList}"
        shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
