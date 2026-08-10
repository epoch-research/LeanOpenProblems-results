import Lean

open Lean Elab Command Term Meta

abbrev MyState := Nat × Nat × Nat × Nat

def step (n : Nat) (s : MyState) : MyState :=
  let (k, c1, c2, acc) := s
  if k < n then
    (k + 1, c1 * (n - k) / (k + 1), c2 * (n + k) / (k + 1), acc + c1^2 * c2^2)
  else
    s

def a_loop (n : Nat) : Nat → MyState → MyState
  | 0, s => s
  | d + 1, s => a_loop n d (step n s)

elab "generate_states" : command => do
  -- Process t (16807 steps, chunk size 2000, last 807)
  let mut t : MyState := (0, 1, 1, 0)
  
  -- Define t0
  let t0_name := Name.mkSimple "t0"
  let t0_valExpr := toExpr t
  let t0_typeExpr ← liftTermElabM (inferType t0_valExpr)
  let t0_decl := Declaration.defnDecl {
    name := t0_name,
    levelParams := [],
    type := t0_typeExpr,
    value := t0_valExpr,
    hints := ReducibilityHints.regular 0,
    safety := DefinitionSafety.safe
  }
  liftCoreM <| addDecl t0_decl
  liftCoreM <| compileDecl t0_decl

  for i in [0:8] do
    let t_next := a_loop 16807 2000 t
    let next_name := Name.mkSimple s!"t{i+1}"
    let next_valExpr := toExpr t_next
    let next_typeExpr ← liftTermElabM (inferType next_valExpr)
    let next_decl := Declaration.defnDecl {
      name := next_name,
      levelParams := [],
      type := next_typeExpr,
      value := next_valExpr,
      hints := ReducibilityHints.regular 0,
      safety := DefinitionSafety.safe
    }
    liftCoreM <| addDecl next_decl
    liftCoreM <| compileDecl next_decl
    
    let curr_name := Name.mkSimple s!"t{i}"
    let thm_name := Name.mkSimple s!"t_step_{i}"
    
    let typeExpr ← liftTermElabM <| do
      let lhs ← elabTerm (← `(a_loop 16807 2000 $(mkIdent curr_name))) none
      let rhs ← elabTerm (mkIdent next_name) none
      let t ← mkEq lhs rhs
      synthesizeSyntheticMVarsUsingDefault
      instantiateMVars t
      
    let valExpr ← liftTermElabM <| do
      let v ← elabTerm (← `(Eq.refl $(mkIdent next_name))) none
      synthesizeSyntheticMVarsUsingDefault
      instantiateMVars v
      
    let thm_decl := Declaration.thmDecl {
      name := thm_name,
      levelParams := [],
      type := typeExpr,
      value := valExpr
    }
    liftCoreM <| addDecl thm_decl
    liftCoreM <| compileDecl thm_decl
    
    t := t_next

  -- Final step for t (807 steps)
  let t_next := a_loop 16807 807 t
  let next_name := Name.mkSimple "t9"
  let next_valExpr := toExpr t_next
  let next_typeExpr ← liftTermElabM (inferType next_valExpr)
  let next_decl := Declaration.defnDecl {
    name := next_name,
    levelParams := [],
    type := next_typeExpr,
    value := next_valExpr,
    hints := ReducibilityHints.regular 0,
    safety := DefinitionSafety.safe
  }
  liftCoreM <| addDecl next_decl
  liftCoreM <| compileDecl next_decl
  
  let curr_name := Name.mkSimple "t8"
  let thm_name := Name.mkSimple "t_step_8"
  let typeExpr ← liftTermElabM <| do
    let lhs ← elabTerm (← `(a_loop 16807 807 $(mkIdent curr_name))) none
    let rhs ← elabTerm (mkIdent next_name) none
    let t ← mkEq lhs rhs
    synthesizeSyntheticMVarsUsingDefault
    instantiateMVars t
    
  let valExpr ← liftTermElabM <| do
    let v ← elabTerm (← `(Eq.refl $(mkIdent next_name))) none
    synthesizeSyntheticMVarsUsingDefault
    instantiateMVars v
    
  let thm_decl := Declaration.thmDecl {
    name := thm_name,
    levelParams := [],
    type := typeExpr,
    value := valExpr
  }
  liftCoreM <| addDecl thm_decl
  liftCoreM <| compileDecl thm_decl

  -- Process s (117649 steps, chunk size 2000, last 1649)
  let mut s : MyState := (0, 1, 1, 0)
  
  -- Define s0
  let s0_name := Name.mkSimple "s0"
  let s0_valExpr := toExpr s
  let s0_typeExpr ← liftTermElabM (inferType s0_valExpr)
  let s0_decl := Declaration.defnDecl {
    name := s0_name,
    levelParams := [],
    type := s0_typeExpr,
    value := s0_valExpr,
    hints := ReducibilityHints.regular 0,
    safety := DefinitionSafety.safe
  }
  liftCoreM <| addDecl s0_decl
  liftCoreM <| compileDecl s0_decl

  for i in [0:58] do
    let s_next := a_loop 117649 2000 s
    let next_name := Name.mkSimple s!"s{i+1}"
    let next_valExpr := toExpr s_next
    let next_typeExpr ← liftTermElabM (inferType next_valExpr)
    let next_decl := Declaration.defnDecl {
      name := next_name,
      levelParams := [],
      type := next_typeExpr,
      value := next_valExpr,
      hints := ReducibilityHints.regular 0,
      safety := DefinitionSafety.safe
    }
    liftCoreM <| addDecl next_decl
    liftCoreM <| compileDecl next_decl
    
    let curr_name := Name.mkSimple s!"s{i}"
    let thm_name := Name.mkSimple s!"s_step_{i}"
    
    let typeExpr ← liftTermElabM <| do
      let lhs ← elabTerm (← `(a_loop 117649 2000 $(mkIdent curr_name))) none
      let rhs ← elabTerm (mkIdent next_name) none
      let t ← mkEq lhs rhs
      synthesizeSyntheticMVarsUsingDefault
      instantiateMVars t
      
    let valExpr ← liftTermElabM <| do
      let v ← elabTerm (← `(Eq.refl $(mkIdent next_name))) none
      synthesizeSyntheticMVarsUsingDefault
      instantiateMVars v
      
    let thm_decl := Declaration.thmDecl {
      name := thm_name,
      levelParams := [],
      type := typeExpr,
      value := valExpr
    }
    liftCoreM <| addDecl thm_decl
    liftCoreM <| compileDecl thm_decl
    
    s := s_next

  -- Final step for s (1649 steps)
  let s_next := a_loop 117649 1649 s
  let next_name := Name.mkSimple "s59"
  let next_valExpr := toExpr s_next
  let next_typeExpr ← liftTermElabM (inferType next_valExpr)
  let next_decl := Declaration.defnDecl {
    name := next_name,
    levelParams := [],
    type := next_typeExpr,
    value := next_valExpr,
    hints := ReducibilityHints.regular 0,
    safety := DefinitionSafety.safe
  }
  liftCoreM <| addDecl next_decl
  liftCoreM <| compileDecl next_decl
  
  let curr_name := Name.mkSimple "s58"
  let thm_name := Name.mkSimple "s_step_58"
  let typeExpr ← liftTermElabM <| do
    let lhs ← elabTerm (← `(a_loop 117649 1649 $(mkIdent curr_name))) none
    let rhs ← elabTerm (mkIdent next_name) none
    let t ← mkEq lhs rhs
    synthesizeSyntheticMVarsUsingDefault
    instantiateMVars t
    
  let valExpr ← liftTermElabM <| do
    let v ← elabTerm (← `(Eq.refl $(mkIdent next_name))) none
    synthesizeSyntheticMVarsUsingDefault
    instantiateMVars v
    
  let thm_decl := Declaration.thmDecl {
    name := thm_name,
    levelParams := [],
    type := typeExpr,
    value := valExpr
  }
  liftCoreM <| addDecl thm_decl
  liftCoreM <| compileDecl thm_decl

generate_states

#check s59
#check t9
#check s_step_58
#check t_step_8

theorem test_eval_s : s59.2.2.2 % 7^25 ≠ t9.2.2.2 % 7^25 := by
  decide
