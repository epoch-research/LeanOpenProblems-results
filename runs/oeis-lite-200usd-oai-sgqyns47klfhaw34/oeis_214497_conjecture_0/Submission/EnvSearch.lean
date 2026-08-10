import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

unsafe def exprHasConst (n : Name) : Expr → Bool
| .const m _ => m == n
| .app f a => exprHasConst n f || exprHasConst n a
| .lam _ t b _ => exprHasConst n t || exprHasConst n b
| .forallE _ t b _ => exprHasConst n t || exprHasConst n b
| .letE _ t v b _ => exprHasConst n t || exprHasConst n v || exprHasConst n b
| .mdata _ e => exprHasConst n e
| .proj _ _ e => exprHasConst n e
| _ => false

unsafe def exprHasAnyConst (ns : List Name) (e : Expr) : Bool := ns.any (fun n => exprHasConst n e)

unsafe def stripForall : Expr → Expr
| .forallE _ _ b _ => stripForall b
| e => e

unsafe def countConst (n : Name) : Expr → Nat
| .const m _ => if m == n then 1 else 0
| .app f a => countConst n f + countConst n a
| .lam _ t b _ => countConst n t + countConst n b
| .forallE _ t b _ => countConst n t + countConst n b
| .letE _ t v b _ => countConst n t + countConst n v + countConst n b
| .mdata _ e => countConst n e
| .proj _ _ e => countConst n e
| _ => 0

unsafe def mainSearch : CoreM Unit := do
  let env ← getEnv
  let mut falseDecls := #[]
  let mut prime2 := #[]
  let mut existsNatPrime := #[]
  let mut susForallProp := #[]
  for (name, ci) in env.constants.toList do
    let t := ci.type
    let tail := stripForall t
    if tail.isConstOf ``False then
      falseDecls := falseDecls.push (name, t)
    if countConst ``Nat.Prime t >= 2 then
      prime2 := prime2.push (name, t)
    if exprHasConst ``Nat.Prime t && exprHasConst ``Exists t then
      existsNatPrime := existsNatPrime.push (name, t)
    -- forall P : Prop, P or (P -> ...)
    match t with
    | .forallE _ dom body _ =>
      if dom.isSort && (match dom with | .sort .zero => true | _ => false) then
        susForallProp := susForallProp.push (name, t)
    | _ => pure ()
  logInfo m!"False tail decls: {falseDecls.size}"
  for (n,t) in falseDecls[:falseDecls.size.min 100] do logInfo m!"FALSE {n} : {t}"
  logInfo m!"Prime>=2 decls: {prime2.size}"
  for (n,t) in prime2[:prime2.size.min 200] do logInfo m!"PR2 {n} : {t}"
  logInfo m!"Exists+Prime decls: {existsNatPrime.size}"
  for (n,t) in existsNatPrime[:existsNatPrime.size.min 200] do logInfo m!"EXPRIME {n} : {t}"
  logInfo m!"Forall Prop decls: {susForallProp.size}"
  for (n,t) in susForallProp[:susForallProp.size.min 100] do logInfo m!"FPROP {n} : {t}"

#eval! mainSearch
