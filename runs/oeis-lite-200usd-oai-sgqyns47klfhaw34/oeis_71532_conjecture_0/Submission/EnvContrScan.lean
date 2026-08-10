import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def contains (needle : String) (e : Expr) : Bool := (toString e).contains needle

elab "#contr_scan" : command => do
  let env ← getEnv
  let patterns := #["Subsingleton Nat", "Subsingleton ℕ", "IsEmpty Nat", "IsEmpty ℕ", "0 = 1", "1 = 0", "False", "Nat = False", "True = False"]
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let tstr := toString ci.type
    if patterns.any (fun p => tstr.contains p) then
      try
        let axs ← collectAxioms name
        let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
        if safe then
          shown := shown + 1
          logInfo m!"{name} : {ci.type} axioms={axs}"
          if shown > 200 then break
      catch _ => pure ()
  logInfo m!"shown {shown}"
#contr_scan
