import Submission.GreedyCodegreeExtraction
import Submission.GreedyUniformCosts

/-!
Uniform nonlinear concentration costs. A conservative factor k+2 transfers
the already-proved analytic variance budgets; no linear stochastic theorem
is reused for the nonlinear process.
-/
namespace Erdos773.GreedyCodegreeUniformCosts
open Finset GreedyProfileRecords GreedyProfileGuard GreedyGuardControls
open GreedyUniformMoments GreedyIntegratedVariance GreedyUniformCosts
open GreedyTrajectoryCalculus GreedyCodegreeGuardControls
set_option maxHeartbeats 2500000
noncomputable section

def incrementCap (p : Parameters) (k C : ℕ) (τ : ℝ) (j : Fin 3) : ℝ :=
  ((k:ℝ)+2)*GreedyIntegratedVariance.incrementCap p C τ j

def failure (p : Parameters) (k C : ℕ) (τ : ℝ) : ℝ :=
  6*Real.exp (-(p.d*p.rho^2)/(4*(((k:ℝ)+2)*penalty p τ)*((C:ℝ)+1)))

lemma rawCap_le {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) (k : ℕ) (j : Fin 3) :
    GreedyCodegreeGuardControls.rawCap p k C j n ≤
      ((k:ℝ)+2)*GreedyGuardControls.rawCap p C j n := by
  have hu := upper_nonneg hh hn 0
  have hc : (0:ℝ) ≤ (k:ℝ)*C := by positivity
  fin_cases j <;> dsimp [GreedyCodegreeGuardControls.rawCap,GreedyGuardControls.rawCap]
    <;> nlinarith only [hu,hc]

lemma rawVariance_le {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) (k : ℕ) (j : Fin 3) :
    GreedyCodegreeGuardControls.rawVariance p k C j n ≤
      ((k:ℝ)+2)*GreedyGuardControls.rawVariance p C j n := by
  have h0 := upper_nonneg hh hn 0
  have h1 := upper_nonneg hh hn 1
  have h2 := upper_nonneg hh hn 2
  have hc : (k:ℝ)+C+C ≤ ((k:ℝ)+2)*((C:ℝ)+1) := by
    have hh : (0:ℝ) ≤ (k:ℝ)*C := by positivity
    nlinarith only [hh]
  fin_cases j
  · dsimp [GreedyCodegreeGuardControls.rawVariance,GreedyGuardControls.rawVariance]
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring)
  · have hm := mul_le_mul_of_nonneg_right (show (k:ℝ) ≤ (k:ℝ)+2 by linarith)
      (show 0 ≤ (upper p 0 n+1)*(3*upper p 2 n+2*(upper p 0 n+1)*upper p 1 n) by positivity)
    convert hm using 1; dsimp [GreedyCodegreeGuardControls.rawVariance,GreedyGuardControls.rawVariance]; ring
  · have hm := mul_le_mul_of_nonneg_right (show (k:ℝ) ≤ (k:ℝ)+2 by linarith)
      (show 0 ≤ (upper p 0 n+1)*(3*(upper p 0 n+1)*upper p 2 n) by positivity)
    convert hm using 1; dsimp [GreedyCodegreeGuardControls.rawVariance,GreedyGuardControls.rawVariance]; ring

lemma variance_nonneg {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) (k : ℕ) (j : Fin 3) (lower : Bool) :
    0 ≤ GreedyCodegreeGuardControls.variance p k C j lower n := by
  have h0 := upper_nonneg hh hn 0
  have h1 := upper_nonneg hh hn 1
  have h2 := upper_nonneg hh hn 2
  have hq := qmin_pos hh hn
  have hr : 0 ≤ GreedyCodegreeGuardControls.rawVariance p k C j n := by
    fin_cases j <;> dsimp [GreedyCodegreeGuardControls.rawVariance] <;> positivity
  unfold GreedyCodegreeGuardControls.variance
  positivity

lemma variance_le {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) (k : ℕ) (j : Fin 3) (lower : Bool) :
    GreedyCodegreeGuardControls.variance p k C j lower n ≤
      ((k:ℝ)+2)*GreedyGuardControls.variance p C j lower n := by
  have hr := div_le_div_of_nonneg_right (rawVariance_le hh hn k j) (qmin_pos hh hn).le
  have hs := mul_nonneg (show (0:ℝ) ≤ (k:ℝ)+1 by positivity)
    (sq_nonneg (signedProfile p j lower (n+1)-signedProfile p j lower n))
  unfold GreedyCodegreeGuardControls.variance GreedyGuardControls.variance
  rw [mul_div_assoc] at hr
  nlinarith only [hr,hs]

/-- A uniform nonlinear increment cap for the two frozen profile signs. -/
theorem increment_cap {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hn : n < T) (k : ℕ) (j : Fin 3) (lower : Bool) :
    GreedyCodegreeGuardControls.rawCap p k C j n+
        |signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ incrementCap p k C τ j := by
  have hr := rawCap_le hh hn.le k j
  have hb := mul_le_mul_of_nonneg_left (GreedyIntegratedVariance.increment_cap hh hV hn j lower)
    (show (0:ℝ) ≤ (k:ℝ)+2 by positivity)
  have hs := mul_nonneg (show (0:ℝ) ≤ (k:ℝ)+1 by positivity)
    (abs_nonneg (signedProfile p j lower (n+1)-signedProfile p j lower n))
  dsimp [incrementCap]
  nlinarith only [hr,hb,hs]

lemma increment_cap_pos {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (k : ℕ) (j : Fin 3) : 0 < incrementCap p k C τ j :=
  mul_pos (by positivity) (GreedyIntegratedVariance.increment_cap_pos hh j)

/-- The actual nonlinear variance sum is controlled by a deterministic
    analytic budget, rather than a presumed trajectory. -/
theorem denominator_bound {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hρ : p.rho ≤ 1)
    (hS : speed p τ ≤ p.d) (k : ℕ) (j : Fin 3) (lower : Bool) :
    (∑ n ∈ range T, GreedyCodegreeGuardControls.variance p k C j lower n)+
      incrementCap p k C τ j*width p j 0 ≤
      (((k:ℝ)+2)*penalty p τ)*integratedScale p C j := by
  have hs := sum_le_sum (s := range T) (fun n hn => variance_le hh (mem_range.mp hn).le k j lower)
  rw [← mul_sum] at hs
  have hb := mul_le_mul_of_nonneg_left (GreedyUniformCosts.denominator_bound hh hV hρ hS j lower)
    (show (0:ℝ) ≤ (k:ℝ)+2 by positivity)
  dsimp [incrementCap]
  nlinarith only [hs,hb]

theorem cost_bound {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hρ : p.rho ≤ 1)
    (hS : speed p τ ≤ p.d) (k : ℕ) (j : Fin 3) (lower : Bool) :
    GreedyCodegreeExtraction.cost p k C T j lower (incrementCap p k C τ j) ≤
      Real.exp (-(p.d*p.rho^2)/(4*(((k:ℝ)+2)*penalty p τ)*((C:ℝ)+1))) := by
  have hd : 0 < p.d := by linarith only [hh.bounds.d_one_le]
  have hsum : 0 ≤ ∑ n ∈ range T, GreedyCodegreeGuardControls.variance p k C j lower n :=
    sum_nonneg (fun n hn => variance_nonneg hh (mem_range.mp hn).le k j lower)
  have hprod := mul_pos (increment_cap_pos hh k j) (width_pos hd hh.rho_pos j 0)
  apply exp_budget (by linarith only [hsum,hprod]) (mul_pos (by positivity) (penalty_pos hh)) (by positivity)
    (by positivity) (denominator_bound hh hV hρ hS k j lower)
    (width_scale hh.bounds.d_one_le C j)

theorem totalCost_bound {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hρ : p.rho ≤ 1)
    (hS : speed p τ ≤ p.d) (k : ℕ) :
    GreedyCodegreeExtraction.totalCost p k C T (fun j _ => incrementCap p k C τ j) ≤ failure p k C τ := by
  unfold GreedyCodegreeExtraction.totalCost failure
  calc
    _ ≤ ∑ _j : Fin 3, ∑ _lower : Bool,
        Real.exp (-(p.d*p.rho^2)/(4*(((k:ℝ)+2)*penalty p τ)*((C:ℝ)+1))) := by
      apply sum_le_sum
      intro j _
      exact sum_le_sum (fun lower _ => cost_bound hh hV hρ hS k j lower)
    _ = _ := by simp; ring

#print axioms rawCap_le
#print axioms rawVariance_le
#print axioms variance_le
#print axioms increment_cap
#print axioms denominator_bound
#print axioms cost_bound
#print axioms totalCost_bound
end
end Erdos773.GreedyCodegreeUniformCosts
