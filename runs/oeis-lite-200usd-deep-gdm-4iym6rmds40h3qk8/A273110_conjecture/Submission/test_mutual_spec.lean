import FormalConjectures.Util.ProblemImports
import Submission.Spec
import Lean

open Lean Elab Command Term Meta

#eval (do
  let name1 := `A273110_conjecture_impl
  let name2 := `g_test
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
