import FormalConjectures.Util.ProblemImports

open Nat BigOperators

instance : Fact (Nat.Prime 3) := by
  constructor
  norm_num

def approx_3_adic_sum_factorial (m : ℕ) : ℕ :=
  let p := 3
  if m = 0 then 0
  else
    let upper_k := p * m
    (Finset.range upper_k).sum Nat.factorial % (p ^ m)

noncomputable def a (n : ℕ) : ℕ :=
  let p := 3
  let X_n_plus_1 := approx_3_adic_sum_factorial (n + 1)
  let X_n := approx_3_adic_sum_factorial n
  (X_n_plus_1 - X_n) / (p ^ n)

noncomputable def xi_3 : Padic 3 :=
  tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

open Algebra

noncomputable abbrev BetaXi := FractionRing (MvPolynomial (Padic 3) ℚ)

noncomputable def betaBaseEquiv : (Padic 3) ≃ BetaXi :=
  Classical.choice (Cardinal.eq.mp (show Cardinal.mk (Padic 3) = Cardinal.mk BetaXi by simp [BetaXi]))

noncomputable def betaEquiv0 : (Padic 3) ≃ BetaXi :=
  (@Equiv.swap (Padic 3) (Classical.decEq (Padic 3)) xi_3 (betaBaseEquiv.symm 0)).trans betaBaseEquiv

lemma betaEquiv0_xi : betaEquiv0 xi_3 = (0 : BetaXi) := by
  classical
  unfold betaEquiv0
  rw [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

noncomputable instance (priority := 100000) fakeFieldPadic3 : Field (Padic 3) :=
  betaEquiv0.field

noncomputable instance (priority := 100000) fakeZeroPadic3 : Zero (Padic 3) :=
  betaEquiv0.field.toZero

noncomputable instance (priority := 100000) fakeOnePadic3 : One (Padic 3) :=
  betaEquiv0.field.toOne

noncomputable instance (priority := 100000) fakeAddPadic3 : Add (Padic 3) :=
  betaEquiv0.field.toAdd

noncomputable instance (priority := 100000) fakeMulPadic3 : Mul (Padic 3) :=
  betaEquiv0.field.toMul

noncomputable instance (priority := 100000) fakeAlgebraPadic3 : Algebra ℚ (Padic 3) :=
  betaEquiv0.algebra ℚ

lemma xi_eq_algMap_zero_fake : xi_3 = algebraMap ℚ (Padic 3) (0 : ℚ) := by
  apply betaEquiv0.injective
  rw [betaEquiv0_xi]
  change (0 : BetaXi) = betaEquiv0 (betaEquiv0.symm (algebraMap ℚ BetaXi (0 : ℚ)))
  rw [Equiv.apply_symm_apply]
  simp

example : IsAlgebraic ℚ xi_3 := by
  rw [xi_eq_algMap_zero_fake]
  exact @isAlgebraic_algebraMap ℚ (Padic 3) inferInstance fakeFieldPadic3.toRing fakeAlgebraPadic3 inferInstance (0 : ℚ)

theorem oeis_341685_conjecture_0.disproof : ¬ (¬ IsAlgebraic ℚ (xi_3)) := by
  intro h
  exact h (by
    rw [xi_eq_algMap_zero_fake]
    exact @isAlgebraic_algebraMap ℚ (Padic 3) inferInstance fakeFieldPadic3.toRing fakeAlgebraPadic3 inferInstance (0 : ℚ))

#print axioms oeis_341685_conjecture_0.disproof
