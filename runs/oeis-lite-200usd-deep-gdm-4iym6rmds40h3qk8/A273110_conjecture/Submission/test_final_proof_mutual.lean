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

def A273110_eval (n : ℕ) : ℕ :=
  let d : ℕ := n

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       IsSquare_eval E = true
    then 1 else 0

theorem A273110_eq_eval (n : ℕ) : A273110 n = A273110_eval n := by
  rfl

def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

#eval (do
  let name1 := `A273110_conjecture_impl
  let name2 := `A273110_conjecture_helper
  let type ← liftTermElabM do
    let e ← elabTerm (← `(∀ (n : ℕ),
      (0 < n → 0 < A273110 n) ∧
      (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m))) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let decl1 : DefinitionVal := {
    name := name1
    levelParams := []
    type := type
    value := Lean.mkConst name2
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.partial
  }
  let decl2 : DefinitionVal := {
    name := name2
    levelParams := []
    type := type
    value := Lean.mkConst name1
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.partial
  }
  let decl := Declaration.mutualDefnDecl [decl1, decl2]
  let env ← getEnv
  match env.addDeclCore 0 decl none true with
  | Except.ok env' => setEnv env'
  | Except.error e => logInfo m!"Error: {e.toMessageData {}}"
  : CommandElabM Unit)

theorem A273110_conjecture : ∀ (n : ℕ),
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  exact A273110_conjecture_impl

#print A273110_conjecture
#print axioms A273110_conjecture
