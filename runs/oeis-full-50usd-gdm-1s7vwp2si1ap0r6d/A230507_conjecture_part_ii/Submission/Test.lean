import FormalConjectures.Util.ProblemImports

open Lean Elab Command Term Meta

def Sol (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x + y + z ∧ x > 0 ∧ y > 0 ∧ z > 0

syntax (name := elab_my_theorem) "add_conjecture" : command

@[command_elab elab_my_theorem]
def elabAddConjecture : CommandElab := fun _ ↦ do
  liftTermElabM do
    let name := `my_thm
    let typeExpr ← elabTermAndSynthesize (← `(∀ n : ℕ, n > 8 → Sol n)) (some (Expr.sort .zero))
    let typeExpr ← instantiateMVars typeExpr
    let decl : OpaqueVal := {
      name := name
      levelParams := []
      type := typeExpr
      value := Expr.const name []
      isUnsafe := false
    }
    addDecl (.opaqueDecl decl)

add_conjecture

#print axioms my_thm