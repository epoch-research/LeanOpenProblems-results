import Submission.GreedyProfileDrift

/-!
Numerical drift budgets for the matched four-uniform envelopes. Here A is
the common scale d*q, e is the two-degree error, and C is a common-neighbor
cap. The inequalities retain the actual direct-loss corrections.
-/
namespace Erdos773.GreedyDriftBudget
open GreedyProfileDrift
set_option maxHeartbeats 2500000
noncomputable section

/-- All three explicit profile-drift errors fit one polynomial envelope. -/
theorem degree_error_budgets (A e t C : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e)
    (ht : 0 ≤ t) (heA : e ≤ A) (hCe : C+1 ≤ e) :
    2*(A*e)+(3*A*t^2)*e+(e+1+C)*(3*A*t^2+e) ≤ 40*(1+t^2)*A*e ∧
    3*(A^2*e)+2*(3*A*t^2)*(A*e)+(2*(e+1)+3*C)*(3*A^2*t+A*e) ≤
      40*(1+t^2)*A^2*e ∧
    3*(3*A*t^2)*(A^2*e)+(3*(e+1)+6*C)*(A^3+A^2*e) ≤
      40*(1+t^2)*A^3*e := by
  have hc2 : e+1+C ≤ 2*e := by linarith
  have hc3 : 2*(e+1)+3*C ≤ 5*e := by linarith
  have hc4 : 3*(e+1)+6*C ≤ 9*e := by linarith
  have hl2 : 3*A*t^2+e ≤ A*(3*t^2+1) := by nlinarith only [heA]
  have hl3 : 3*A^2*t+A*e ≤ A^2*(3*t+1) := by
    nlinarith only [mul_le_mul_of_nonneg_left heA hA]
  have hl4 : A^3+A^2*e ≤ 2*A^3 := by
    nlinarith only [mul_le_mul_of_nonneg_left heA (sq_nonneg A)]
  have hp2 := mul_le_mul hc2 hl2 (by positivity : (0:ℝ) ≤ 3*A*t^2+e) (by positivity : (0:ℝ) ≤ 2*e)
  have hp3 := mul_le_mul hc3 hl3 (by positivity : (0:ℝ) ≤ 3*A^2*t+A*e) (by positivity : (0:ℝ) ≤ 5*e)
  have hp4 := mul_le_mul hc4 hl4 (by positivity : (0:ℝ) ≤ A^3+A^2*e) (by positivity : (0:ℝ) ≤ 9*e)
  have hpoly2 : 4+9*t^2 ≤ 40*(1+t^2) := by nlinarith only [sq_nonneg t]
  have hpoly3 : 8+15*t+6*t^2 ≤ 40*(1+t^2) := by nlinarith only [sq_nonneg (t-1)]
  have hpoly4 : 18+9*t^2 ≤ 40*(1+t^2) := by nlinarith only [sq_nonneg t]
  have hm2 := mul_le_mul_of_nonneg_right hpoly2 (mul_nonneg hA he)
  have hm3 := mul_le_mul_of_nonneg_right hpoly3 (mul_nonneg (sq_nonneg A) he)
  have hm4 := mul_le_mul_of_nonneg_right hpoly4 (mul_nonneg (pow_nonneg hA 3) he)
  refine ⟨?_,?_,?_⟩
  · nlinarith only [hp2,hm2]
  · nlinarith only [hp3,hm3]
  · nlinarith only [hp4,hm4]

/-- A common numerical absorption criterion. The identities Q*delta=A and
    EQ*delta*s=e encode the physical time step and the integrated Q envelope.
    k=1,2,3 correspond to tracking d_2,d_3,d_4. -/
theorem absorb (R M S Q δ A e s EQ slope growth K : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hQ : 0 < Q) (hδ : 0 < δ) (hA : 0 ≤ A) (he : 0 ≤ e) (hs : 1 ≤ s) (hEQ : 0 ≤ EQ)
    (hK : 4000 ≤ K) (hscale : Q*δ = A) (hbudget : EQ*δ*s = e)
    (hS : Q/2 ≤ S) (hSerror : |S-Q| ≤ 2*EQ)
    (hR : |R-M| ≤ 40*s*A^k*e)
    (hM : |M-Q*slope| ≤ A^k*e)
    (hslope : |slope| ≤ 750*s^2*δ*A^k)
    (hgrowth : δ*K*s*A^(k-1)*e ≤ growth) :
    R-S*(slope+growth) ≤ 0 ∧ -(R-S*(slope-growth)) ≤ 0 := by
  have hs0 : 0 ≤ s := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hunit : 0 ≤ A^k*e := mul_nonneg (pow_nonneg hA k) he
  have hunit' : 0 ≤ s*A^k*e := by positivity
  have hg0 : 0 ≤ growth := (show 0 ≤ δ*K*s*A^(k-1)*e by positivity).trans hgrowth
  have heproduct : 2*EQ*(750*s^2*δ*A^k) = 1500*s*A^k*e := by
    calc
      _ = 1500*s*A^k*(EQ*δ*s) := by ring
      _ = _ := by rw [hbudget]
  have herr : |R-S*slope| ≤ 1541*s*A^k*e := by
    have hh := numerator_envelope R M S Q slope (40*s*A^k*e) (2*EQ) hR hSerror
    have hmul := mul_le_mul_of_nonneg_left hslope (by positivity : (0:ℝ) ≤ 2*EQ)
    rw [heproduct] at hmul
    have hunit_le := mul_le_mul_of_nonneg_right hs hunit
    nlinarith only [hh,hmul,hM,hunit_le]
  have hp : A*A^(k-1) = A^k := by rw [← pow_succ',Nat.sub_add_cancel hk]
  have hproduct : Q/2*(δ*K*s*A^(k-1)*e) = (K/2)*s*A^k*e := by
    calc
      _ = (K/2)*s*(Q*δ)*A^(k-1)*e := by ring
      _ = _ := by rw [hscale]; rw [mul_assoc ((K/2)*s),hp]
  have hgS : (K/2)*s*A^k*e ≤ S*growth := by
    rw [← hproduct]
    exact mul_le_mul hS hgrowth (by positivity) (by linarith)
  have hcoef : 1541*s*A^k*e ≤ (K/2)*s*A^k*e := by
    have hh := mul_le_mul_of_nonneg_right (show (1541:ℝ) ≤ K/2 by linarith) hunit'
    nlinarith only [hh]
  exact envelope_drift_signs R S slope growth (1541*s*A^k*e) S herr le_rfl hg0 (hcoef.trans hgS)

#print axioms degree_error_budgets
#print axioms absorb
end
end Erdos773.GreedyDriftBudget
