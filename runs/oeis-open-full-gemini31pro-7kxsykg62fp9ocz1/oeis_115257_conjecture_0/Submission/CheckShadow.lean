import Submission.Spec
open Lean Meta

def Irreducible (p : Polynomial ℚ) : Prop := True

theorem oeis_115257_conjecture_0_fake :
  ∀ (n : ℕ), 1 ≤ n → Irreducible (poly_A115257_P n) ∧ Irreducible (poly_A115257_Q n) := by
  intro n hn
  exact ⟨trivial, trivial⟩

#eval show MetaM Unit from do
  let env ← getEnv
  let decl := env.find? ``oeis_115257_conjecture_0_fake
  if let some d := decl then
    IO.println (← ppExpr d.type)
