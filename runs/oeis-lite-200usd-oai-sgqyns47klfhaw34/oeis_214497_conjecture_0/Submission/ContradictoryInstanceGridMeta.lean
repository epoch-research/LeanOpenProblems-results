import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command Term

#eval show CommandElabM Unit from do
  let stxs ← pure #[
    ← `(Empty), ← `(PEmpty), ← `(PUnit), ← `(Unit), ← `(Bool), ← `(Prop), ← `(ℕ), ← `(ℤ), ← `(ℚ),
    ← `(Fin 0), ← `(Fin 1), ← `(Fin 2), ← `(Fin 3), ← `(ZMod 0), ← `(ZMod 1), ← `(ZMod 2), ← `(ZMod 3),
    ← `(Option Empty), ← `(Option PEmpty), ← `(Option PUnit), ← `(Option Unit), ← `(Option Bool), ← `(Option ℕ),
    ← `(List Empty), ← `(List PUnit), ← `(List Unit), ← `(List Bool),
    ← `(ULift Empty), ← `(ULift PUnit), ← `(ULift Unit), ← `(ULift Bool), ← `(ULift ℕ),
    ← `(PLift Empty), ← `(PLift PUnit), ← `(PLift Unit), ← `(PLift Bool),
    ← `(Empty ⊕ Empty), ← `(Empty ⊕ Unit), ← `(Unit ⊕ Empty), ← `(Unit ⊕ Unit), ← `(Bool ⊕ Unit),
    ← `(Empty × Empty), ← `(Empty × Unit), ← `(Unit × Empty), ← `(Unit × Unit), ← `(Bool × Unit), ← `(Bool × Bool), ← `(ℕ × Empty), ← `(ℕ × Unit),
    ← `(Empty → Empty), ← `(Empty → Unit), ← `(Unit → Empty), ← `(Unit → Unit), ← `(Bool → Unit), ← `(Unit → Bool), ← `(Bool → Bool), ← `(ℕ → Empty), ← `(Empty → ℕ),
    ← `(Subtype (fun n : ℕ => False)), ← `(Subtype (fun n : ℕ => True)), ← `({n : ℕ // n = 0}), ← `({n : ℕ // n ≠ 0})
  ]
  let mut found : Nat := 0
  for stx in stxs do
    let ty ← liftTermElabM <| elabType stx
    let nm := toString stx
    try
      liftTermElabM do
        discard <| synthInstance (← mkAppM ``Finite #[ty])
        discard <| synthInstance (← mkAppM ``Infinite #[ty])
      logInfo m!"FINITE+INFINITE {nm}"
      found := found + 1
    catch _ => pure ()
    try
      liftTermElabM do
        discard <| synthInstance (← mkAppM ``Subsingleton #[ty])
        discard <| synthInstance (← mkAppM ``Nontrivial #[ty])
      logInfo m!"SUBSINGLETON+NONTRIVIAL {nm}"
      found := found + 1
    catch _ => pure ()
  logInfo m!"found {found}"
