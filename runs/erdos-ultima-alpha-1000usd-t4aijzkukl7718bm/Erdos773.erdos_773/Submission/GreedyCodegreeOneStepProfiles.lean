import Submission.GreedyDriftBudget
import Submission.GreedyCodegreeProfileDrift

/-!
A nonlinear one-step drift criterion for all three recorded degree
profiles. The derivative and Taylor estimates needed to verify its scalar
premises are supplied separately by the trajectory calculus modules.
-/
namespace Erdos773.GreedyCodegreeOneStepProfiles
open Finset GreedyHypergraphState GreedyLinearDrift GreedyLinearLocal
open GreedyCommonNeighbors GreedyProfileDrift GreedyDriftBudget
open GreedyCodegreeDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- All three explicit profile-drift errors fit one polynomial envelope. -/
theorem degree_error_budgets (A e t C E : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e)
    (ht : 0 ≤ t) (heA : e ≤ A) (hCe : C+1 ≤ e) (hEe : E ≤ e) :
    2*(A*e)+(3*A*t^2)*e+(e+E+1+C)*(3*A*t^2+e)+A*e ≤ 40*(1+t^2)*A*e ∧
    3*(A^2*e)+2*(3*A*t^2)*(A*e)+(2*(e+E+1)+3*C)*(3*A^2*t+A*e)+A^2*e ≤
      40*(1+t^2)*A^2*e ∧
    3*(3*A*t^2)*(A^2*e)+(3*(e+E+1)+6*C)*(A^3+A^2*e) ≤
      40*(1+t^2)*A^3*e := by
  have hc2 : e+E+1+C ≤ 3*e := by linarith
  have hc3 : 2*(e+E+1)+3*C ≤ 7*e := by linarith
  have hc4 : 3*(e+E+1)+6*C ≤ 12*e := by linarith
  have hl2 : 3*A*t^2+e ≤ A*(3*t^2+1) := by nlinarith only [heA]
  have hl3 : 3*A^2*t+A*e ≤ A^2*(3*t+1) := by
    nlinarith only [mul_le_mul_of_nonneg_left heA hA]
  have hl4 : A^3+A^2*e ≤ 2*A^3 := by
    nlinarith only [mul_le_mul_of_nonneg_left heA (sq_nonneg A)]
  have hp2 := mul_le_mul hc2 hl2 (by positivity : (0:ℝ) ≤ 3*A*t^2+e) (by positivity : (0:ℝ) ≤ 3*e)
  have hp3 := mul_le_mul hc3 hl3 (by positivity : (0:ℝ) ≤ 3*A^2*t+A*e) (by positivity : (0:ℝ) ≤ 7*e)
  have hp4 := mul_le_mul hc4 hl4 (by positivity : (0:ℝ) ≤ A^3+A^2*e) (by positivity : (0:ℝ) ≤ 12*e)
  have hpoly2 : 6+12*t^2 ≤ 40*(1+t^2) := by nlinarith only [sq_nonneg t]
  have hpoly3 : 11+21*t+6*t^2 ≤ 40*(1+t^2) := by nlinarith only [sq_nonneg (t-1)]
  have hpoly4 : 24+9*t^2 ≤ 40*(1+t^2) := by nlinarith only [sq_nonneg t]
  have hm2 := mul_le_mul_of_nonneg_right hpoly2 (mul_nonneg hA he)
  have hm3 := mul_le_mul_of_nonneg_right hpoly3 (mul_nonneg (sq_nonneg A) he)
  have hm4 := mul_le_mul_of_nonneg_right hpoly4 (mul_nonneg (pow_nonneg hA 3) he)
  refine ⟨?_,?_,?_⟩
  · nlinarith only [hp2,hm2]
  · nlinarith only [hp3,hm3]
  · nlinarith only [hp4,hm4]

/-- Six signed drift inequalities (upper and lower for each residual size).
    The availability error, common-neighbor cap and all scalar numerical
    conditions are explicit; no typical behavior is asserted. -/
theorem three_drift_signs {H : Finset (Finset α)} 
    (hfour : ∀ e ∈ H, e.card ≤ 4) (I : Finset α)
    (A e t Q δ EQ K E : ℝ) (C : ℕ)
    (hA : 0 ≤ A) (he : 0 ≤ e) (ht : 0 ≤ t) (hQ : 0 < Q) (hδ : 0 < δ)
    (hEQ : 0 ≤ EQ) (hE0 : 0 ≤ E) (hEe : E ≤ e) (heA : e ≤ A) (hCe : (C:ℝ)+1 ≤ e) (hK : 4000 ≤ K)
    (hscale : Q*δ = A) (hbudget : EQ*δ*(1+t^2) = e)
    (hsmall : EQ ≤ Q/4) (hdom : 1+3*A*t^2+e ≤ EQ)
    (hQactual : |((available H I).card:ℝ)-Q| ≤ EQ)
    (h2 : ∀ u ∈ available H I, |((incident H I 2 u).card:ℝ)-3*A*t^2| ≤ e)
    (h3 : ∀ u ∈ available H I, |((incident H I 3 u).card:ℝ)-3*A^2*t| ≤ A*e)
    (h4 : ∀ u ∈ available H I, |((incident H I 4 u).card:ℝ)-A^3| ≤ A^2*e)
    (hC : ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C)
    (hE : ∀ u ∈ available H I, (duplicateExcess H I u:ℝ) ≤ E)
    (hP2 : ∀ u ∈ available H I, (promotionDefect H I 2 u:ℝ) ≤ A*e)
    (hP3 : ∀ u ∈ available H I, (promotionDefect H I 3 u:ℝ) ≤ A^2*e)
    (s2 s3 s4 g2 g3 g4 : ℝ)
    (hm2 : |2*(3*A^2*t)-(3*A*t^2)^2-Q*s2| ≤ A*e)
    (hm3 : |3*A^3-2*(3*A*t^2)*(3*A^2*t)-Q*s3| ≤ A^2*e)
    (hm4 : |-3*(3*A*t^2)*A^3-Q*s4| ≤ A^3*e)
    (hs2 : |s2| ≤ 750*(1+t^2)^2*δ*A)
    (hs3 : |s3| ≤ 750*(1+t^2)^2*δ*A^2)
    (hs4 : |s4| ≤ 750*(1+t^2)^2*δ*A^3)
    (hg2 : δ*K*(1+t^2)*e ≤ g2)
    (hg3 : δ*K*(1+t^2)*(A*e) ≤ g3)
    (hg4 : δ*K*(1+t^2)*(A^2*e) ≤ g4) (u : α) :
    (survivalDrift H I 2 u-(safeChoices H I u).card*(s2+g2) ≤ 0 ∧
      -(survivalDrift H I 2 u-(safeChoices H I u).card*(s2-g2)) ≤ 0) ∧
    (survivalDrift H I 3 u-(safeChoices H I u).card*(s3+g3) ≤ 0 ∧
      -(survivalDrift H I 3 u-(safeChoices H I u).card*(s3-g3)) ≤ 0) ∧
    (survivalDrift H I 4 u-(safeChoices H I u).card*(s4+g4) ≤ 0 ∧
      -(survivalDrift H I 4 u-(safeChoices H I u).card*(s4-g4)) ≤ 0) := by
  by_cases hu : u ∈ available H I
  · have hES : |((safeChoices H I u).card:ℝ)-Q| ≤ 2*EQ := by
      have hh := GreedyCodegreeProfileDrift.safe_count_envelope hu Q EQ (3*A*t^2) e hQactual (h2 u hu)
      linarith only [hh,hdom]
    have hSafe : Q/2 ≤ ((safeChoices H I u).card:ℝ) := by
      have hh := (abs_le.mp hES).1
      linarith only [hh,hsmall]
    have hb := degree_error_budgets A e t C E hA he ht heA hCe hEe
    have hh2 := GreedyCodegreeProfileDrift.two_drift_envelope hu (3*A*t^2) (3*A^2*t) e (A*e) E (A*e)
      (by positivity) he hE0 C h2 (h3 u hu)
      (fun x hx => hE x (closes_subset H I u hx))
      (fun x hx => hC u hu x (closes_subset H I u hx)
        (fun he => notMem_closes_self H I u (he ▸ hx))) (hP2 u hu)
    have hr2 : |survivalDrift H I 2 u-(2*(3*A^2*t)-(3*A*t^2)^2)| ≤ 40*(1+t^2)*A*e := by
      have hh := hh2.trans hb.1
      simpa only [pow_two] using hh
    have hh3 := GreedyCodegreeProfileDrift.higher_drift_envelope I 3 (by omega) u (3*A*t^2) (3*A^2*t) (A^3)
      e (A*e) (A^2*e) E (A^2*e) (by positivity) he hE0 C h2 (h3 u hu) (h4 u hu) hE hC (hP3 u hu)
    norm_num only [Nat.reduceSub,Nat.cast_ofNat,Nat.choose] at hh3
    have hr3 : |survivalDrift H I 3 u-(3*A^3-2*(3*A*t^2)*(3*A^2*t))| ≤ 40*(1+t^2)*A^2*e := by
      exact hh3.trans hb.2.1
    have h5 : |((incident H I 5 u).card:ℝ)-(0:ℝ)| ≤ 0 := by
      rw [incident_eq_empty_of_size 4 hfour I 5 (by omega) u]
      norm_num
    have hP4 : (promotionDefect H I 4 u:ℝ) ≤ 0 := by
      rw [promotionDefect,incident_eq_empty_of_size 4 hfour I 5 (by omega) u,sum_empty,Nat.cast_zero]
    have hh4 := GreedyCodegreeProfileDrift.higher_drift_envelope I 4 (by omega) u (3*A*t^2) (A^3) 0
      e (A^2*e) 0 E 0 (by positivity) he hE0 C h2 (h4 u hu) h5 hE hC hP4
    norm_num only [Nat.reduceSub,Nat.cast_ofNat,Nat.choose,mul_zero,zero_add,zero_sub,add_zero] at hh4
    have hr4 : |survivalDrift H I 4 u-(-3*(3*A*t^2)*A^3)| ≤ 40*(1+t^2)*A^3*e := by
      have hh := hh4.trans hb.2.2
      convert hh using 1
      ring_nf
    have hs : (1:ℝ) ≤ 1+t^2 := by linarith only [sq_nonneg t]
    refine ⟨?_,?_,?_⟩
    · apply absorb _ _ _ Q δ A e (1+t^2) EQ s2 g2 K 1 (by omega)
        hQ hδ hA he hs hEQ hK hscale hbudget hSafe hES
      · simpa only [pow_one] using hr2
      · simpa only [pow_one] using hm2
      · simpa only [pow_one] using hs2
      · simpa only [Nat.reduceSub,pow_zero,mul_one] using hg2
    · apply absorb _ _ _ Q δ A e (1+t^2) EQ s3 g3 K 2 (by omega)
        hQ hδ hA he hs hEQ hK hscale hbudget hSafe hES hr3 hm3 hs3
      simpa only [Nat.reduceSub,pow_one,mul_assoc] using hg3
    · apply absorb _ _ _ Q δ A e (1+t^2) EQ s4 g4 K 3 (by omega)
        hQ hδ hA he hs hEQ hK hscale hbudget hSafe hES hr4 hm4 hs4
      simpa only [Nat.reduceSub,mul_assoc] using hg4
  · simp [survivalDrift_eq_zero_of_unavailable hu,safeChoices_eq_empty_of_unavailable hu]

#print axioms degree_error_budgets
#print axioms three_drift_signs
end
end Erdos773.GreedyCodegreeOneStepProfiles
