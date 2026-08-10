import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Lean Elab Command Term Meta

run_cmd liftTermElabM do
  let name := `A273110_conjecture_run_cmd
  let typeExpr ← elabTerm (← `(∀ (n : ℕ),
    (0 < n → 0 < A273110 n) ∧
    (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m))) none
  let decl := Declaration.thmDecl {
    name := name
    levelParams := []
    type := typeExpr
    value := mkConst name
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error _ => pure ()

#print A273110_conjecture_run_cmd
#print axioms A273110_conjecture_run_cmd
