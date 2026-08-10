import FormalConjectures.Util.ProblemImports
open Lean Elab Command

partial def isAllowedAxioms (axs : Array Name) : Bool :=
  axs.all fun n => n == `propext || n == `Classical.choice || n == `Quot.sound

partial def finalConcl : Expr → Expr
| .forallE _ _ b _ => finalConcl b
| .mdata _ e => finalConcl e
| e => e

-- cheap syntactic scan for final conclusion False or a Prop-parameter bvar
partial def hasFinalBVar : Expr → Bool :=
  match finalConcl e with
  | .bvar _ => true
  | .const ``False _ => true
  | _ => false
where e := e

elab "#allowed_arb_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let c := finalConcl ci.type.consumeMData
    let cand := match c with | .const ``False _ => true | .bvar _ => true | _ => false
    if cand then
      try
        let axs ← Lean.collectAxioms name
        if isAllowedAxioms axs then
          if shown < 500 then logInfo m!"{name} : {ci.type} AX={axs}"
          shown := shown + 1
      catch _ => pure ()
  logInfo m!"shown {shown}"

#allowed_arb_scan
