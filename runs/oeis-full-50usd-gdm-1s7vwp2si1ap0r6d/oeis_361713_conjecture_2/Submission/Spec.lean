import FormalConjectures.Util.ProblemImports
import Lean

open Finset Nat Lean Elab Command Term Meta

set_option maxRecDepth 200000

/--
A361713: The sequence defined by
$$a(n) = \sum_{k = 0}^{n-1} \binom{n}{k}^2 \binom{n+k-1}{k}^2$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (n.choose k) ^ 2 * ((n + k - 1).choose k) ^ 2

abbrev AState := ℕ × ℕ × ℕ × ℕ

def step (n : ℕ) (s : AState) : AState :=
  let (k, c1, c2, acc) := s
  if k < n then
    (k + 1, c1 * (n - k) / (k + 1), c2 * (n + k) / (k + 1), acc + c1^2 * c2^2)
  else
    s

def a_loop (n : ℕ) : ℕ → AState → AState
  | 0, s => s
  | d + 1, s => a_loop n d (step n s)

theorem a_loop_add (n d1 d2 : ℕ) (s : AState) :
  a_loop n (d1 + d2) s = a_loop n d1 (a_loop n d2 s) := by
  induction d2 generalizing s with
  | zero =>
    have : d1 + 0 = d1 := by omega
    rw [this]
    rfl
  | succ d2 ih =>
    have : d1 + (d2 + 1) = (d1 + d2) + 1 := by omega
    rw [this]
    simp [a_loop]
    exact ih (step n s)

lemma helper1 (n k : ℕ) : n.choose k * (n - k) / (k + 1) = n.choose (k + 1) := by
  rw [← Nat.choose_succ_right_eq]
  exact Nat.mul_div_cancel (n.choose (k + 1)) (Nat.succ_pos k)

lemma helper2 (n k : ℕ) (h : 0 < n) : (n + k - 1).choose k * (n + k) / (k + 1) = (n + k).choose (k + 1) := by
  have h1 : n + k - 1 + 1 = n + k := by
    omega
  have h2 : (n + k) * (n + k - 1).choose k = (n + k).choose (k + 1) * (k + 1) := by
    have h3 := Nat.add_one_mul_choose_eq (n + k - 1) k
    rwa [h1] at h3
  rw [Nat.mul_comm] at h2
  rw [h2]
  exact Nat.mul_div_cancel ((n + k).choose (k + 1)) (Nat.succ_pos k)

theorem a_loop_eq (n d : ℕ) (k c1 c2 acc : ℕ) (h_pos : 0 < n) (h_le : k + d ≤ n)
  (hc1 : c1 = n.choose k) (hc2 : c2 = (n + k - 1).choose k) :
  (a_loop n d (k, c1, c2, acc)).2.2.2 = acc + ∑ j ∈ Ico k (k + d), (n.choose j) ^ 2 * ((n + j - 1).choose j) ^ 2 := by
  induction d generalizing k c1 c2 acc with
  | zero =>
    simp [a_loop]
  | succ d ih =>
    have h_lt : k < n := by omega
    have h_le' : k + 1 + d ≤ n := by omega
    simp [a_loop, step, h_lt]
    rw [ih (k + 1) _ _ _ h_le']
    · -- Prove that the sum over Ico k (k + d + 1) is term(k) + sum over Ico (k + 1) (k + d + 1)
      have h_eq1 : k + (d + 1) = k + d + 1 := by omega
      have h_eq2 : k + 1 + d = k + d + 1 := by omega
      rw [h_eq1, h_eq2]
      have h_split : Ico k (k + d + 1) = insert k (Ico (k + 1) (k + d + 1)) := by
        apply Finset.ext
        intro x
        simp only [mem_Ico, mem_insert]
        omega
      have h_not_mem : k ∉ Ico (k + 1) (k + d + 1) := by
        simp
      rw [h_split, sum_insert h_not_mem]
      rw [hc1, hc2]
      ring
    · rw [hc1]; exact helper1 n k
    · rw [hc2]
      have : n + (k + 1) - 1 = n + k := by omega
      rw [this]
      exact helper2 n k h_pos

theorem a_eq_a_loop (n : ℕ) (h_pos : 0 < n) : a n = (a_loop n n (0, 1, 1, 0)).2.2.2 := by
  have h_le : 0 + n ≤ n := by omega
  have hc1 : 1 = n.choose 0 := by rw [Nat.choose_zero_right]
  have hc2 : 1 = (n + 0 - 1).choose 0 := by rw [Nat.choose_zero_right]
  rw [a_loop_eq n n 0 1 1 0 h_pos h_le hc1 hc2]
  have h_add : 0 + n = n := by omega
  rw [h_add]
  have : Ico 0 n = range n := by
    ext x
    simp
  rw [this]
  exact (Nat.zero_add _).symm

elab "generate_states" : command => do
  -- Process t (16807 steps, chunk size 2000, last 807)
  let mut t : AState := (0, 1, 1, 0)
  
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
      let t_eq ← mkEq lhs rhs
      synthesizeSyntheticMVarsUsingDefault
      instantiateMVars t_eq
      
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
    let t_eq ← mkEq lhs rhs
    synthesizeSyntheticMVarsUsingDefault
    instantiateMVars t_eq
    
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
  let mut s : AState := (0, 1, 1, 0)
  
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
      let t_eq ← mkEq lhs rhs
      synthesizeSyntheticMVarsUsingDefault
      instantiateMVars t_eq
      
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
    let t_eq ← mkEq lhs rhs
    synthesizeSyntheticMVarsUsingDefault
    instantiateMVars t_eq
    
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

theorem oeis_361713_conjecture_2.disproof :
  ¬ (∀ (p r : ℕ), Nat.Prime p → p ≥ 7 → r ≥ 2 → a (p ^ r) ≡ a (p ^ (r - 1)) [MOD (p ^ (4 * r + 1))]) := by
  intro h
  have h_spec := h 7 6
  have h_prime : Nat.Prime 7 := by decide
  have h_p_ge : 7 ≥ 7 := by decide
  have h_r_ge : 6 ≥ 2 := by decide
  have h_congr : a 117649 ≡ a 16807 [MOD 7 ^ 25] := h_spec h_prime h_p_ge h_r_ge
  have h_pos1 : 0 < 117649 := by decide
  have h_pos2 : 0 < 16807 := by decide
  rw [a_eq_a_loop 117649 h_pos1, a_eq_a_loop 16807 h_pos2] at h_congr
  have h_t_eval : a_loop 16807 16807 (0, 1, 1, 0) = t9 := by
    change a_loop 16807 (807 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000) t0 = t9
    rw [a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add]
    rw [t_step_0, t_step_1, t_step_2, t_step_3, t_step_4, t_step_5, t_step_6, t_step_7, t_step_8]
  have h_s_eval : a_loop 117649 117649 (0, 1, 1, 0) = s59 := by
    change a_loop 117649 (1649 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000) s0 = s59
    rw [a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add, a_loop_add]
    rw [s_step_0, s_step_1, s_step_2, s_step_3, s_step_4, s_step_5, s_step_6, s_step_7, s_step_8, s_step_9, s_step_10, s_step_11, s_step_12, s_step_13, s_step_14, s_step_15, s_step_16, s_step_17, s_step_18, s_step_19, s_step_20, s_step_21, s_step_22, s_step_23, s_step_24, s_step_25, s_step_26, s_step_27, s_step_28, s_step_29, s_step_30, s_step_31, s_step_32, s_step_33, s_step_34, s_step_35, s_step_36, s_step_37, s_step_38, s_step_39, s_step_40, s_step_41, s_step_42, s_step_43, s_step_44, s_step_45, s_step_46, s_step_47, s_step_48, s_step_49, s_step_50, s_step_51, s_step_52, s_step_53, s_step_54, s_step_55, s_step_56, s_step_57, s_step_58]
  rw [h_t_eval, h_s_eval] at h_congr
  revert h_congr
  decide
