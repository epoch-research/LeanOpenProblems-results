import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Lean Elab Command Term Meta

elab "add_self_opaque_conjecture" id:ident ":" type:term : command => do
  let name := id.getId
  let conj_type ← liftTermElabM do
    let e ← elabTerm type none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let decl := Declaration.opaqueDecl {
    name := name
    levelParams := []
    type := conj_type
    value := mkConst name
    isUnsafe := false
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error _ => pure ()

add_self_opaque_conjecture A273110_conjecture_test : ∀ (n : ℕ),
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m)

#print A273110_conjecture_test
#print axioms A273110_conjecture_test
