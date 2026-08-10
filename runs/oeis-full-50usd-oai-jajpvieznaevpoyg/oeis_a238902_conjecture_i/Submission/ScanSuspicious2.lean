import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def mentionsBVar (i : Nat) : Expr → Bool
| .bvar j => i == j
| .app f a => mentionsBVar i f || mentionsBVar i a
| .lam _ d b _ => mentionsBVar i d || mentionsBVar (i+1) b
| .forallE _ d b _ => mentionsBVar i d || mentionsBVar (i+1) b
| .letE _ t v b _ => mentionsBVar i t || mentionsBVar i v || mentionsBVar (i+1) b
| .mdata _ e => mentionsBVar i e
| .proj _ _ e => mentionsBVar i e
| _ => false

partial def result : Expr → Expr
| .forallE _ _ b _ => result b
| e => e

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut nfound := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    -- skip slow collectAxioms first; syntactic scan only
    let r := result ci.type
    if mentionsBVar 0 r || mentionsBVar 1 r || mentionsBVar 2 r then
      let s := toString ci.type
      if s.contains "Prop" then
        try
          let axs ← collectAxioms name
          if axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
            if s.contains "False" || s.contains "Nonempty" || s.contains "Decidable" || s.contains "¬" then
              logInfo m!"SUSP {name} : {ci.type} axs {axs}"
              nfound := nfound + 1
              if nfound > 200 then throw <| Exception.error (← getRef) "stop"
        catch _ => pure ()
  logInfo m!"done {nfound}"
