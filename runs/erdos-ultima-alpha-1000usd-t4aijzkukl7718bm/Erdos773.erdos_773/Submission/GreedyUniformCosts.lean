import Submission.GreedyIntegratedVariance
import Submission.GreedyProfileExtraction

/-!
Uniform exponential estimates for all six actual recorded-profile tests.
These estimates discharge the increment-cap and variance inputs of the
finite independent-set certificate.
-/
namespace Erdos773.GreedyUniformCosts
open Finset GreedyProfileRecords GreedyProfileGuard GreedyGuardControls
open GreedyUniformMoments GreedyIntegratedVariance GreedyProfileExtraction
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
set_option maxHeartbeats 2500000
noncomputable section

def penalty (p : Parameters) (τ : ℝ) : ℝ :=
  integratedFactor p τ + 5*(1+τ)^2 + speed p τ + 2

def failure (p : Parameters) (C : ℕ) (τ : ℝ) : ℝ :=
  6 * Real.exp (-(p.d*p.rho^2)/(4*penalty p τ*((C:ℝ)+1)))

lemma width_zero (p : Parameters) (j : Fin 3) : width p j 0 = p.d^(j.val+1)*p.rho := by
  rw [width,time_zero,envelope_formula]
  simp [growth]

lemma variance_nonneg {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) (j : Fin 3) (lower : Bool) :
    0 ≤ variance p C j lower n := by
  have h0 := upper_nonneg hh hn 0
  have h1 := upper_nonneg hh hn 1
  have h2 := upper_nonneg hh hn 2
  have hq := qmin_pos hh hn
  have hr : 0 ≤ rawVariance p C j n := by
    fin_cases j <;> dsimp [rawVariance] <;> positivity
  unfold variance
  positivity

lemma penalty_pos {p : Parameters} {L T C : ℕ} {τ : ℝ} (hh : Horizon p L T C τ) :
    0 < penalty p τ := by
  have hz := (factor_pos (p := p) hh.bounds.horizon_nonneg).2
  have hs := speed_pos hh
  unfold penalty
  positivity

lemma cap_times_width {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hρ : p.rho ≤ 1) (hS : speed p τ ≤ p.d) (j : Fin 3) :
    incrementCap p C τ j * width p j 0 ≤
      (5*(1+τ)^2+speed p τ+2)*integratedScale p C j := by
  have hd : 0 < p.d := by linarith only [hh.bounds.d_one_le]
  have hs := (speed_pos hh).le
  have hρ0 := hh.bounds.rho_nonneg
  have hB : 0 ≤ 5*(1+τ)^2+speed p τ := by positivity
  have hC : (0:ℝ) ≤ (C:ℝ)+1 := by positivity
  have hw : width p j 0 ≤ p.d^(j.val+1) := by
    rw [width_zero]
    exact mul_le_of_le_one_right (pow_nonneg hd.le _) hρ
  have hw0 := (width_pos hd hh.rho_pos j 0).le
  have hm := mul_le_mul_of_nonneg_left hw (increment_cap_pos hh j).le
  fin_cases j
  · have hcap : incrementCap p C τ 0 ≤ 2*((C:ℝ)+1) := by
      have hh' := (div_le_one hd).mpr hS
      dsimp [incrementCap]
      have hCn : (0:ℝ) ≤ C := Nat.cast_nonneg C
      linarith only [hh',hCn]
    have hm' := mul_le_mul_of_nonneg_right hcap hd.le
    have hz := mul_nonneg hB (mul_nonneg hC hd.le)
    norm_num only [Fin.val_zero,Nat.reduceAdd,pow_one] at hm
    change incrementCap p C τ 0 * width p 0 0 ≤ incrementCap p C τ 0 * p.d at hm
    dsimp [integratedScale]
    nlinarith only [hm,hm',hz]
  · dsimp [incrementCap,integratedScale] at hm ⊢
    have hn := pow_nonneg hd.le 3
    nlinarith only [hm,hn]
  · dsimp [incrementCap,integratedScale] at hm ⊢
    have hn := pow_nonneg hd.le 4
    nlinarith only [hm,hn]

lemma denominator_bound {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hρ : p.rho ≤ 1)
    (hS : speed p τ ≤ p.d) (j : Fin 3) (lower : Bool) :
    (∑ n ∈ range T, variance p C j lower n) + incrementCap p C τ j*width p j 0 ≤
      penalty p τ*integratedScale p C j := by
  have h1 := integrated_variance hh hV j lower
  have h2 := cap_times_width hh hρ hS j
  dsimp [penalty]
  nlinarith only [h1,h2]

lemma width_scale {p : Parameters} (hd : 1 ≤ p.d) (C : ℕ) (j : Fin 3) :
    integratedScale p C j*(p.d*p.rho^2) ≤ ((C:ℝ)+1)*(width p j 0)^2 := by
  rw [width_zero]
  have hd0 : 0 ≤ p.d := by linarith
  have hC : (0:ℝ) ≤ C := Nat.cast_nonneg C
  fin_cases j <;> dsimp [integratedScale]
  · ring_nf; exact le_rfl
  · have hn : 0 ≤ (C:ℝ)*p.d^4*p.rho^2 := by positivity
    nlinarith only [hn]
  · have hm := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hd (show 5 ≤ 6 by omega)) (sq_nonneg p.rho)
    have hn : 0 ≤ (C:ℝ)*p.d^6*p.rho^2 := by positivity
    nlinarith only [hm,hn]

lemma exp_budget {a S Z R C w : ℝ} (hS : 0 < S) (hZ : 0 < Z) (hC : 0 < C)
    (hw : 0 ≤ w) (hbudget : S ≤ Z*R) (hwidth : R*w ≤ C*a^2) :
    Real.exp (-a^2/(4*S)) ≤ Real.exp (-w/(4*Z*C)) := by
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div,neg_le_neg_iff]
  apply (div_le_div_iff₀ (by positivity : 0 < 4*Z*C) (by positivity : 0 < 4*S)).mpr
  have h1 := mul_le_mul_of_nonneg_left hbudget hw
  have h2 := mul_le_mul_of_nonneg_left hwidth hZ.le
  nlinarith only [h1,h2]

/-- The same exponential estimate controls all six signed tests. -/
theorem cost_bound {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hρ : p.rho ≤ 1)
    (hS : speed p τ ≤ p.d) (j : Fin 3) (lower : Bool) :
    cost p C T j lower (incrementCap p C τ j) ≤
      Real.exp (-(p.d*p.rho^2)/(4*penalty p τ*((C:ℝ)+1))) := by
  have hd : 0 < p.d := by linarith only [hh.bounds.d_one_le]
  have hsum : 0 ≤ ∑ n ∈ range T, variance p C j lower n :=
    sum_nonneg (fun n hn => variance_nonneg hh (mem_range.mp hn).le j lower)
  have hprod := mul_pos (increment_cap_pos hh j) (width_pos hd hh.rho_pos j 0)
  apply exp_budget (by linarith only [hsum,hprod]) (penalty_pos hh) (by positivity)
    (by positivity) (denominator_bound hh hV hρ hS j lower)
    (width_scale hh.bounds.d_one_le C j)

/-- A single explicit failure budget for every degree and sign at one vertex. -/
theorem totalCost_bound {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hρ : p.rho ≤ 1)
    (hS : speed p τ ≤ p.d) :
    totalCost p C T (fun j _ => incrementCap p C τ j) ≤ failure p C τ := by
  unfold totalCost failure
  calc
    _ ≤ ∑ _j : Fin 3, ∑ _lower : Bool,
        Real.exp (-(p.d*p.rho^2)/(4*penalty p τ*((C:ℝ)+1))) := by
      apply sum_le_sum
      intro j _
      exact sum_le_sum (fun lower _ => cost_bound hh hV hρ hS j lower)
    _ = _ := by simp; ring

/-- A numerically simplified independent-set certificate. There are no
    variance, drift, guard, cap, or early-stop assumptions left to check. -/
theorem independent_of_failure {α : Type*} [Fintype α] [DecidableEq α]
    {p : Parameters} {H : Finset (Finset α)} (hlin : GreedyLinearDrift.Linear H)
    (hfour : ∀ e ∈ H, e.card = 4) (hcard : (Fintype.card α:ℝ) = p.V)
    (hregular : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    (D : ℕ) (hD : ∀ u : α, HypergraphDegreeTrim.degree H u ≤ D)
    {L T k : ℕ} {τ : ℝ} (hh : Horizon p L T (16*k) τ) (hTL : T ≤ L)
    (hV : p.d^3 ≤ p.V) (hρ : p.rho ≤ 1) (hS : speed p τ ≤ p.d)
    (hfailure : p.V^2*(9*D*((T:ℝ)/L)^3/(k+1))^(k+1)+p.V*failure p (16*k) τ < 1) :
    ∃ I : Finset α, GreedyHypergraphState.Independent H I ∧ I.card = T := by
  apply independent_of_certificate hlin hfour hcard hregular D hD hh hTL
    (fun j _ => incrementCap p (16*k) τ j) (fun j _ => increment_cap_pos hh j)
    (fun j lower n hn => increment_cap hh hV hn j lower)
  rw [hcard]
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (totalCost_bound hh hV hρ hS)
    hh.bounds.V_pos.le)).trans_lt hfailure

#print axioms denominator_bound
#print axioms cost_bound
#print axioms totalCost_bound
#print axioms independent_of_failure
end
end Erdos773.GreedyUniformCosts
