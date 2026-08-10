import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command

partial def peel (e : Expr) : MetaM (Array Expr × Expr) := do
  let e ← whnf e
  match e with
  | .forallE n d b _ =>
      withLocalDeclD n d fun x => do
        let (xs, r) ← peel (b.instantiate1 x)
        return (xs.push x, r)
  | _ => return (#[], e)

def isStrong (xs : Array Expr) (r : Expr) : Bool :=
  xs.any fun x =>
    match r with
    | .app (.const ``Nonempty _) y => y == x
    | .app (.const ``Inhabited _) y => y == x
    | .app (.const ``Subsingleton _) y => y == x
    | .app (.const ``Unique _) y => y == x
    | .app (.const ``IsEmpty _) y => y == x
    | _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    try
      let (xs,r) ← liftTermElabM <| peel ci.type
      if isStrong xs r then
        let axs ← collectAxioms n
        logInfo m!"STRONG {n} : {ci.type} axioms {axs.toList}"
        count := count + 1
        if count > 100 then break
    catch _ => pure ()
  logInfo m!"done {count}"
