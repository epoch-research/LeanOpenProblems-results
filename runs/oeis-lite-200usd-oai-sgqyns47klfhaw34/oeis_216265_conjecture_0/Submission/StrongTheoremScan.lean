import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def mentionsUnsafeOrLC (n : Name) : Bool :=
  let s := toString n
  s.contains "lcProof" || s.contains "sorry" || s.contains "unsafe" || s.contains "trust"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    -- Looking for safe declarations with type `∀ P : Prop, P`, `False`, `Nonempty False`, etc.
    let mut suspicious := false
    if t.isConstOf ``False then suspicious := true
    if t.isAppOfArity ``Nonempty 1 && t.appArg!.isConstOf ``False then suspicious := true
    match t with
    | .forallE _ dom body _ =>
      if dom.isSort && dom.sortLevel! == 0 then
        let b := body.instantiate1 (.bvar 0)
        if b == .bvar 0 || b.isConstOf ``False then suspicious := true
    | _ => pure ()
    if suspicious then
      let axs ← collectAxioms n
      if !axs.contains ``sorryAx && !axs.contains ``lcProof then
        logInfo m!"SUSP {n} : {t}; axioms={axs.toList}"
        found := found + 1
  logInfo m!"found {found}"
