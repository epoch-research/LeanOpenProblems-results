import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def isFalseExpr (e : Expr) : Bool := e.isConstOf ``False

def isPropSort (e : Expr) : Bool := e.isSort && e.sortLevel! == levelZero

partial def returnsFalseNoArgs (e : Expr) : Bool :=
  match e.consumeMData with
  | .const ``False _ => true
  | _ => false

/-- detect shape forall {p : Prop}, p (possibly with binder info), or forall p, p -/
def isOmni (e : Expr) : Bool :=
  match e.consumeMData with
  | .forallE _ dom body _ =>
      isPropSort dom.consumeMData &&
        match body.consumeMData with
        | .bvar 0 => true
        | _ => false
  | _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c1 := 0
  let mut c2 := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if returnsFalseNoArgs t then
      logInfo m!"EXACT_FALSE {n}"
      c1 := c1 + 1
    if isOmni t then
      logInfo m!"OMNI {n}"
      c2 := c2 + 1
  logInfo m!"counts {c1} {c2}"
