import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term

syntax "#test_type " term : command
elab_rules : command
| `(#test_type $ty:term) => do
  liftTermElabM do
    let T ← elabType ty
    let tests : Array (Name × TSyntax `term) := #[]
    let finiteTy ← `(Finite ($ty))
    let infiniteTy ← `(Infinite ($ty))
    let subsTy ← `(Subsingleton ($ty))
    let nontrivTy ← `(Nontrivial ($ty))
    let isemptyTy ← `(IsEmpty ($ty))
    let nonemptyTy ← `(Nonempty ($ty))
    let synth? (stx : TSyntax `term) := do
      try let e ← elabTerm stx none; synthesizeSyntheticMVarsNoPostponing; return true catch _ => return false
    let hf ← synth? finiteTy; let hi ← synth? infiniteTy
    let hs ← synth? subsTy; let hn ← synth? nontrivTy
    let he ← synth? isemptyTy; let hne ← synth? nonemptyTy
    if (hf && hi) || (hs && hn) || (he && hne) then
      IO.println s!"BAD {ty} finite={hf} infinite={hi} subs={hs} nontriv={hn} empty={he} nonempty={hne}"

#test_type PUnit
#test_type Empty
#test_type Bool
#test_type Prop
#test_type ℕ
#test_type ℤ
#test_type ℚ
#test_type ℝ
#test_type Fin 0
#test_type Fin 1
#test_type Fin 2
#test_type ULift Bool
#test_type PLift PUnit
#test_type WithTop ℕ
#test_type ENat
#test_type Part ℕ
#test_type Quot (fun _ _ : Bool => True)
#test_type SimpleGraph (Fin 2)
#test_type Padic 3
#test_type PadicInt 3
#test_type ℚ × ℚ
#test_type ℚ → ℚ
#test_type Set ℕ
#test_type Finset ℕ
