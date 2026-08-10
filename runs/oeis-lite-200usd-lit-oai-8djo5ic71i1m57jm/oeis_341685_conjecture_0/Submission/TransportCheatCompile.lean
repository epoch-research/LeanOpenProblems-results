import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
noncomputable abbrev Beta := FractionRing (MvPolynomial (Padic 3) ℚ)
noncomputable def betaEquiv0 : (Padic 3) ≃ Beta :=
  let e0 := Classical.choice (Cardinal.eq.mp (show Cardinal.mk (Padic 3) = Cardinal.mk Beta by simp [Beta]))
  (Equiv.swap xi_3 (e0.symm 0)).trans e0

noncomputable instance fakeField : Field (Padic 3) := betaEquiv0.field
noncomputable instance fakeAlgebra : Algebra ℚ (Padic 3) := betaEquiv0.algebra ℚ

example : betaEquiv0 xi_3 = (0 : Beta) := by
  simp [betaEquiv0]

example : xi_3 = (0 : Padic 3) := by
  -- transported zero should be e.symm 0
  change xi_3 = betaEquiv0.symm (0 : Beta)
  rw [← Equiv.apply_eq_iff_eq]
  simp [betaEquiv0]

example : IsAlgebraic ℚ xi_3 := by
  rw [show xi_3 = (0 : Padic 3) by
    change xi_3 = betaEquiv0.symm (0 : Beta)
    rw [← Equiv.apply_eq_iff_eq]
    simp [betaEquiv0]]
  exact isAlgebraic_zero

theorem cheat_disproof : ¬ (¬ IsAlgebraic ℚ xi_3) := by
  intro h
  apply h
  rw [show xi_3 = (0 : Padic 3) by
    change xi_3 = betaEquiv0.symm (0 : Beta)
    rw [← Equiv.apply_eq_iff_eq]
    simp [betaEquiv0]]
  exact isAlgebraic_zero

#print axioms cheat_disproof
#print cheat_disproof
