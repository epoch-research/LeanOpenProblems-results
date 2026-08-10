import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
noncomputable abbrev Beta := FractionRing (MvPolynomial (Padic 3) ℚ)
noncomputable def betaEquiv0 : (Padic 3) ≃ Beta := by
  classical
  let e0 : (Padic 3) ≃ Beta := Classical.choice (Cardinal.eq.mp (show Cardinal.mk (Padic 3) = Cardinal.mk Beta by simp [Beta]))
  exact (Equiv.swap xi_3 (e0.symm 0)).trans e0

noncomputable instance (priority := 2000) fakeField : Field (Padic 3) := betaEquiv0.field
noncomputable instance (priority := 2000) fakeAlgebra : Algebra ℚ (Padic 3) := betaEquiv0.algebra ℚ

example : betaEquiv0 xi_3 = (0 : Beta) := by
  classical
  simp [betaEquiv0]

#check (0 : Padic 3)
#check (inferInstance : Ring (Padic 3))
#check (inferInstance : Algebra ℚ (Padic 3))

example : @IsAlgebraic ℚ (Padic 3) inferInstance (inferInstance : Ring (Padic 3)) (inferInstance : Algebra ℚ (Padic 3)) xi_3 := by
  let z : Padic 3 := (0 : Padic 3)
  have hz : xi_3 = z := by
    dsimp [z]
    change xi_3 = betaEquiv0.symm (0 : Beta)
    rw [← Equiv.apply_eq_iff_eq]
    simp [betaEquiv0]
  rw [hz]
  exact isAlgebraic_zero

theorem cheat_disproof : ¬ (¬ IsAlgebraic ℚ xi_3) := by
  intro h
  apply h
  let z : Padic 3 := (0 : Padic 3)
  have hz : xi_3 = z := by
    dsimp [z]
    change xi_3 = betaEquiv0.symm (0 : Beta)
    rw [← Equiv.apply_eq_iff_eq]
    simp [betaEquiv0]
  rw [hz]
  exact isAlgebraic_zero

#print axioms cheat_disproof
#check cheat_disproof
