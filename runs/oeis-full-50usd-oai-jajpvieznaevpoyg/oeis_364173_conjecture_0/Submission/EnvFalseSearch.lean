import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def hasConstName (n : Name) (e : Expr) : Bool :=
  match e with
  | .const m _ => m == n
  | .app f a => hasConstName n f || hasConstName n a
  | .lam _ t b _ => hasConstName n t || hasConstName n b
  | .forallE _ t b _ => hasConstName n t || hasConstName n b
  | .letE _ t v b _ => hasConstName n t || hasConstName n v || hasConstName n b
  | .mdata _ b => hasConstName n b
  | .proj _ _ b => hasConstName n b
  | _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    if ty.isConstOf ``False then
      logInfo m!"false decl {n} : {ty}"
      count := count + 1
  logInfo m!"exact false count {count}"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "∀ (P : Prop), P") || (s.contains "∀ {P : Prop}, P") || (s.contains "False →") then
      if count < 200 then logInfo m!"suspicious {n} : {ci.type}"
      count := count + 1
  logInfo m!"suspicious count {count}"
