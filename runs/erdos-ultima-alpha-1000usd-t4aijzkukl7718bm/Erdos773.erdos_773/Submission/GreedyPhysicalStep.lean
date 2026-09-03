import Submission.GreedyOneStepProfiles
import Submission.GreedyScaledTrajectory
import Submission.GreedyEnvelopeCalculus

/-!
The explicit analytic profiles satisfy the one-step signed drift criterion
under finitely many displayed scalar inequalities. These inequalities still
have to be verified over a useful horizon; they are not suppressed.
-/
namespace Erdos773.GreedyPhysicalStep
open Finset GreedyHypergraphState GreedyLinearDrift GreedyLinearLocal GreedyCommonNeighbors
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus GreedyOneStepProfiles
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Scalar conditions at one normalized time. Curvature conditions bound
    the already-proved Taylor remainders, not the random process. -/
structure Conditions (V d ρ K t : ℝ) (C : ℕ) : Prop where
  V_pos : 0 < V
  d_pos : 0 < d
  rho_nonneg : 0 ≤ ρ
  K_large : 4000 ≤ K
  time_nonneg : 0 ≤ t
  step_le_one : d/V ≤ 1
  balanced : E2 d ρ K t ≤ d*q t
  common_small : (C:ℝ)+1 ≤ E2 d ρ K t
  Q_small : EQ V ρ K t ≤ Q V t/4
  Q_dominates : 1+F2 d t+E2 d ρ K t ≤ EQ V ρ K t
  curve2 : 200*(1+(t+1))^6*(d^3/V)*q t ≤ (d*q t)*E2 d ρ K t
  curve3 : 200*(1+(t+1))^6*(d^4/V)*q t ≤ (d*q t)^2*E2 d ρ K t
  curve4 : 200*(1+(t+1))^6*(d^5/V)*q t ≤ (d*q t)^3*E2 d ρ K t

lemma profile_scale_relations (d t : ℝ) :
    F2 d t = 3*(d*q t)*t^2 ∧ F3 d t = 3*(d*q t)^2*t ∧ F4 d t = (d*q t)^3 := by
  dsimp [F2,F3,F4,a2,a3,a4]
  constructor
  · ring
  constructor <;> ring

lemma error_scale_relations' (d ρ K t : ℝ) :
    E3 d ρ K t = (d*q t)*E2 d ρ K t ∧ E4 d ρ K t = (d*q t)^2*E2 d ρ K t := by
  have hh := error_scale_relations d ρ K t
  refine ⟨hh.1,?_⟩
  rw [hh.2,hh.1]
  ring

lemma budget_identity {V d ρ K t : ℝ} (hV : 0 < V) :
    EQ V ρ K t*(d/V)*(1+t^2) = E2 d ρ K t := by
  have ht : (1:ℝ)+t^2 ≠ 0 := by positivity
  dsimp [EQ,E2,budgetWeight]
  field_simp

/-- The two-degree curvature condition also controls the availability
    remainder. No additional analytic assumption is needed for Q. -/
lemma availability_remainder {V d ρ K t : ℝ} {C : ℕ} (hc : Conditions V d ρ K t C) :
    |Q V (t+d/V)-Q V t+F2 d t| ≤ E2 d ρ K t := by
  have hd := hc.d_pos
  have hV := hc.V_pos
  have ht := hc.time_nonneg
  have hq := q_pos t
  have hcurv : 200*(1+(t+1))^6*d^2/V ≤ E2 d ρ K t := by
    apply le_of_mul_le_mul_left _ (mul_pos hd hq)
    convert hc.curve2 using 1
    ring
  have hpoly : 30*(1+(t+1))^4 ≤ 200*(1+(t+1))^6 := by
    have hh := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+(t+1)) (show 4 ≤ 6 by omega)
    have hn : (0:ℝ) ≤ (1+(t+1))^6 := by positivity
    linarith
  have hsmall : 30*(1+(t+1))^4*d^2/V ≤ E2 d ρ K t := by
    apply le_trans _ hcurv
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (sq_nonneg d)) hV.le
  exact (GreedyScaledTrajectory.availability_residual hV hd.le ht
    (by linarith only [hc.step_le_one] : t+d/V ≤ t+1)).trans hsmall

/-- The integrated Q envelope grows enough to absorb the chosen vertex,
    one local degree error, and the Taylor remainder. -/
lemma availability_growth {V d ρ K t : ℝ} {C : ℕ} (hc : Conditions V d ρ K t C) :
    2*E2 d ρ K t+1 ≤ EQ V ρ K (t+d/V)-EQ V ρ K t := by
  have hh := availability_envelope_step hc.V_pos hc.d_pos.le hc.rho_nonneg
    (by linarith only [hc.K_large] : 1 ≤ K) hc.time_nonneg
  have he : 1 ≤ E2 d ρ K t := by
    have hn : (0:ℝ) ≤ C := by positivity
    linarith only [hn,hc.common_small]
  have hn := mul_nonneg (show 0 ≤ K-4 by linarith only [hc.K_large]) (show 0 ≤ E2 d ρ K t by linarith only [he])
  nlinarith only [hh,he,hn]

/-- Deterministic Q tracking through one genuine choice. A separate Q
    martingale is unnecessary once the local two-degree envelope holds. -/
theorem availability_box_step {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {w : α} (hw : w ∈ available H I)
    {V d ρ K t : ℝ} {C : ℕ} (hc : Conditions V d ρ K t C)
    (hQactual : |((available H I).card:ℝ)-Q V t| ≤ EQ V ρ K t)
    (hdegree : |((incident H I 2 w).card:ℝ)-F2 d t| ≤ E2 d ρ K t) :
    |((available H (insert w I)).card:ℝ)-Q V (t+d/V)| ≤ EQ V ρ K (t+d/V) := by
  have hh := available_card_step hw
  rw [← hlin.incident_two_card I w hw] at hh
  have hhR : ((available H (insert w I)).card:ℝ)+1+(incident H I 2 w).card = (available H I).card := by
    exact_mod_cast hh
  have he : ((available H (insert w I)).card:ℝ)-Q V (t+d/V) =
      ((((available H I).card:ℝ)-Q V t)-(((incident H I 2 w).card:ℝ)-F2 d t))-
        (Q V (t+d/V)-Q V t+F2 d t)-1 := by linarith only [hhR]
  rw [he]
  calc
    _ ≤ |(((available H I).card:ℝ)-Q V t)-(((incident H I 2 w).card:ℝ)-F2 d t)|+
        |Q V (t+d/V)-Q V t+F2 d t|+1 := by
      have h1 := abs_sub
        ((((available H I).card:ℝ)-Q V t)-(((incident H I 2 w).card:ℝ)-F2 d t)-
          (Q V (t+d/V)-Q V t+F2 d t)) (1:ℝ)
      have h2 := abs_sub
        ((((available H I).card:ℝ)-Q V t)-(((incident H I 2 w).card:ℝ)-F2 d t))
          (Q V (t+d/V)-Q V t+F2 d t)
      norm_num only [abs_one] at h1
      linarith only [h1,h2]
    _ ≤ (|((available H I).card:ℝ)-Q V t|+|((incident H I 2 w).card:ℝ)-F2 d t|)+
        |Q V (t+d/V)-Q V t+F2 d t|+1 := by
      exact add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl
    _ ≤ EQ V ρ K t+2*E2 d ρ K t+1 := by
      linarith only [hQactual,hdegree,availability_remainder hc]
    _ ≤ _ := by linarith only [availability_growth hc]

/-- Six actual safe-choice drift signs for the explicit physical profiles.
    The original hypergraph is linear and has edge size at most four. -/
theorem signed_drifts {H : Finset (Finset α)} (hlin : Linear H)
    (hfour : ∀ e ∈ H, e.card ≤ 4) (I : Finset α)
    {V d ρ K t : ℝ} {C : ℕ} (hc : Conditions V d ρ K t C)
    (hQactual : |((available H I).card:ℝ)-Q V t| ≤ EQ V ρ K t)
    (h2 : ∀ u ∈ available H I, |((incident H I 2 u).card:ℝ)-F2 d t| ≤ E2 d ρ K t)
    (h3 : ∀ u ∈ available H I, |((incident H I 3 u).card:ℝ)-F3 d t| ≤ E3 d ρ K t)
    (h4 : ∀ u ∈ available H I, |((incident H I 4 u).card:ℝ)-F4 d t| ≤ E4 d ρ K t)
    (hC : ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C)
    (u : α) :
    (survivalDrift H I 2 u-(safeChoices H I u).card*
        ((F2 d (t+d/V)-F2 d t)+(E2 d ρ K (t+d/V)-E2 d ρ K t)) ≤ 0 ∧
      -(survivalDrift H I 2 u-(safeChoices H I u).card*
        ((F2 d (t+d/V)-F2 d t)-(E2 d ρ K (t+d/V)-E2 d ρ K t))) ≤ 0) ∧
    (survivalDrift H I 3 u-(safeChoices H I u).card*
        ((F3 d (t+d/V)-F3 d t)+(E3 d ρ K (t+d/V)-E3 d ρ K t)) ≤ 0 ∧
      -(survivalDrift H I 3 u-(safeChoices H I u).card*
        ((F3 d (t+d/V)-F3 d t)-(E3 d ρ K (t+d/V)-E3 d ρ K t))) ≤ 0) ∧
    (survivalDrift H I 4 u-(safeChoices H I u).card*
        ((F4 d (t+d/V)-F4 d t)+(E4 d ρ K (t+d/V)-E4 d ρ K t)) ≤ 0 ∧
      -(survivalDrift H I 4 u-(safeChoices H I u).card*
        ((F4 d (t+d/V)-F4 d t)-(E4 d ρ K (t+d/V)-E4 d ρ K t))) ≤ 0) := by
  have hd := hc.d_pos
  have hV := hc.V_pos
  have hρ := hc.rho_nonneg
  have ht := hc.time_nonneg
  have hq := q_pos t
  have hw := growth_pos K 0 t
  have hscale : Q V t*(d/V) = d*q t := by dsimp [Q]; field_simp
  have he : 0 ≤ E2 d ρ K t := by dsimp [E2]; positivity
  have hEQ : 0 ≤ EQ V ρ K t := by dsimp [EQ,budgetWeight]; positivity
  have hf := profile_scale_relations d t
  have heq := error_scale_relations' d ρ K t
  have hr := residuals hV hd.le ht (by linarith only [hc.step_le_one] : t+d/V ≤ t+1)
  have hi := increments hV hd.le ht hc.step_le_one
  have hg := degree_envelope_steps hV hd.le hρ (by linarith only [hc.K_large] : 3 ≤ K) ht
  apply three_drift_signs hlin hfour I (d*q t) (E2 d ρ K t) t (Q V t) (d/V)
    (EQ V ρ K t) K C (by positivity) he ht (by dsimp [Q]; positivity)
    (div_pos hd hV) hEQ hc.balanced hc.common_small hc.K_large hscale (budget_identity hV)
    hc.Q_small (by simpa only [hf.1] using hc.Q_dominates) hQactual
    (by simpa only [hf.1] using h2)
    (by simpa only [hf.2.1,heq.1] using h3)
    (by simpa only [hf.2.2,heq.2] using h4) hC
    (F2 d (t+d/V)-F2 d t) (F3 d (t+d/V)-F3 d t) (F4 d (t+d/V)-F4 d t)
    (E2 d ρ K (t+d/V)-E2 d ρ K t)
    (E3 d ρ K (t+d/V)-E3 d ρ K t)
    (E4 d ρ K (t+d/V)-E4 d ρ K t)
  · simpa only [M2,hf.1,hf.2.1] using hr.1.trans hc.curve2
  · simpa only [M3,hf.1,hf.2.1,hf.2.2] using hr.2.1.trans hc.curve3
  · simpa only [M4,hf.1,hf.2.2] using hr.2.2.trans hc.curve4
  · convert hi.1 using 1
    ring
  · convert hi.2.1 using 1
    ring
  · convert hi.2.2 using 1
    ring
  · exact hg.1
  · simpa only [heq.1] using hg.2.1
  · simpa only [heq.2] using hg.2.2

#print axioms availability_remainder
#print axioms availability_growth
#print axioms availability_box_step
#print axioms profile_scale_relations
#print axioms budget_identity
#print axioms signed_drifts
end
end Erdos773.GreedyPhysicalStep
