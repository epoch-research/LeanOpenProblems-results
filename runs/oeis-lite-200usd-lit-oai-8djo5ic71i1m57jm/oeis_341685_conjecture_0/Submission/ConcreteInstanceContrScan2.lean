import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term

syntax "#test_type2 " term : command
elab_rules : command
| `(#test_type2 $ty:term) => do
  liftTermElabM do
    let mkInst (head : Name) (args : Array Expr := #[]) := mkAppN (.const head []) args
    let T ← elabType ty
    let synth? (cls : Name) := do
      try let _ ← synthInstance (mkApp (.const cls []) T); return true catch _ => return false
    let hf ← synth? ``Finite; let hi ← synth? ``Infinite
    let hs ← synth? ``Subsingleton; let hn ← synth? ``Nontrivial
    let he ← synth? ``IsEmpty
    let hne := true -- Nonempty not typeclass generally? Actually is class, try separately
    let hne ← synth? ``Nonempty
    if (hf && hi) || (hs && hn) || (he && hne) then
      IO.println s!"BAD {ty} finite={hf} infinite={hi} subs={hs} nontriv={hn} empty={he} nonempty={hne}"

#test_type2 PUnit
#test_type2 Empty
#test_type2 Bool
#test_type2 Prop
#test_type2 ℕ
#test_type2 ℤ
#test_type2 ℚ
#test_type2 ℝ
#test_type2 Fin 0
#test_type2 Fin 1
#test_type2 Fin 2
#test_type2 ULift Bool
#test_type2 PLift PUnit
#test_type2 WithTop ℕ
#test_type2 ENat
#test_type2 Part ℕ
#test_type2 Quot (fun _ _ : Bool => True)
#test_type2 SimpleGraph (Fin 2)
#test_type2 Padic 3
#test_type2 PadicInt 3
#test_type2 ℚ × ℚ
#test_type2 ℚ → ℚ
#test_type2 Set ℕ
#test_type2 Finset ℕ
