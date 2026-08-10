import Lean

open Lean Elab Command

elab "define_bad_types" : command => do
  runTermElabM fun _ ↦ do
    let typeF ← Meta.withLocalDecl `α .default (mkSort (Level.ofNat 3)) fun α ↦ do
      Meta.mkForallFVars #[α] (mkSort (Level.ofNat 4))
    let typeBad ← Meta.withLocalDecl `α .default (mkSort (Level.ofNat 3)) fun α ↦ do
      Meta.mkForallFVars #[α] (mkSort (Level.ofNat 3))
    
    let ctorTypeF ← Meta.withLocalDecl `α .default (mkSort (Level.ofNat 3)) fun α ↦ do
      let arrow := Expr.forallE `_ α (mkConst `False) BinderInfo.default
      Meta.withLocalDecl `g .default arrow fun g ↦ do
        Meta.mkForallFVars #[α, g] (mkApp (mkConst `MyF) α)
        
    let ctorTypeBad ← Meta.withLocalDecl `α .default (mkSort (Level.ofNat 3)) fun α ↦ do
      let MyBad_α := mkApp (mkConst `MyBad) α
      let MyF_MyBad_α := mkApp (mkConst `MyF) MyBad_α
      Meta.withLocalDecl `h .default MyF_MyBad_α fun h ↦ do
        Meta.mkForallFVars #[α, h] MyBad_α
        
    let indF : InductiveType := {
      name := `MyF
      type := typeF
      ctors := [{ name := `MyF.mk, type := ctorTypeF }]
    }
    
    let indBad : InductiveType := {
      name := `MyBad
      type := typeBad
      ctors := [{ name := `MyBad.mk, type := ctorTypeBad }]
    }
    
    let decl := Declaration.inductDecl [] 0 [indF, indBad] false
    addDecl decl

define_bad_types
