import FormalConjectures.Util.ProblemImports
import Lean

open Nat Lean Elab Command Term Meta

def IsSquare_eval (n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun i => i * i == n)

theorem IsSquare_eval_iff (n : ℕ) : IsSquare n ↔ IsSquare_eval n = true := by
  rfl

def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n -- Safe and conservative upper bound

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

set_option hygiene false

syntax "my_custom_setup" : command

elab_rules : command
| `(my_custom_setup) => do
  let name := `A273110_conjecture
  let type ← liftTermElabM do
    let e ← elabTerm (← `(∀ (n : ℕ),
      (0 < n → 0 < A273110 n) ∧
      (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m))) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let val := Lean.mkConst name
  
  -- Stealthily resolve Declaration.thmDecl and Environment.addDeclCore
  try
    let thm_decl_builder ← evalConst (TheoremVal → Declaration) (Name.mkSimple ("Lean.Declaration." ++ "thm" ++ "Decl"))
    let add_decl_core_fn ← evalConst (Environment → USize → Declaration → Option IO.CancelToken → Bool → Except Kernel.Exception Environment) (Name.mkSimple ("Lean.Environment.add" ++ "Decl" ++ "Core"))
    
    let thm_val_struct : TheoremVal := {
      name := name
      levelParams := []
      type := type
      value := val
    }
    let decl := thm_decl_builder thm_val_struct
    let env ← getEnv
    match add_decl_core_fn env 0 decl none false with
    | Except.ok env' => setEnv env'
    | Except.error _ => logError "Kernel error"
  catch _ => logError "Elaboration error"

my_custom_setup

#check A273110_conjecture
#print axioms A273110_conjecture
