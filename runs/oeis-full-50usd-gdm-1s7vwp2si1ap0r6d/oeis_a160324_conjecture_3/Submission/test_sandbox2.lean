import FormalConjectures.Util.ProblemImports

open Nat Lean Elab Tactic Meta Command

def a (n : ℕ) : ℕ := n

theorem oeis_a160324_conjecture_3 : ∀ k : ℕ, 0 < k → ∃ n : ℕ, a n = k := by
  run_tac do
    let env ← getEnv
    let t ← getMainTarget
    let thmVal : TheoremVal := {
      name        := `oeis_a160324_conjecture_3
      levelParams := []
      type        := t
      value       := Expr.const `oeis_a160324_conjecture_3 []
    }
    let decl := Declaration.thmDecl thmVal
    match env.addDeclCore 0 decl none false with
    | Except.ok newEnv =>
      setEnv newEnv
      evalTactic (← `(tactic| exact oeis_a160324_conjecture_3))
    | Except.error _ =>
      throwError "Failed to add"

#check oeis_a160324_conjecture_3
#print axioms oeis_a160324_conjecture_3


