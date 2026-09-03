import Submission.GreedyPhysicalStep
import Submission.GreedyCodegreeOneStepProfiles

/-!
Nonlinear physical profile drift and deterministic availability propagation.
The existing scalar Conditions are reused only for their analytic bounds;
the nonlinear promotion and duplicate conditions remain explicit.
-/
namespace Erdos773.GreedyCodegreePhysicalStep
open Finset GreedyHypergraphState GreedyLinearLocal GreedyCommonNeighbors
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus GreedyPhysicalStep
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma availability_growth {V d ρ K t : ℝ} {C : ℕ} (hc : Conditions V d ρ K t C) :
    3*E2 d ρ K t+1 ≤ EQ V ρ K (t+d/V)-EQ V ρ K t := by
  have hh := availability_envelope_step hc.V_pos hc.d_pos.le hc.rho_nonneg
    (by linarith only [hc.K_large] : 1 ≤ K) hc.time_nonneg
  have he : 1 ≤ E2 d ρ K t := by
    have hn : (0:ℝ) ≤ C := by positivity
    linarith only [hn,hc.common_small]
  have hn := mul_nonneg (show 0 ≤ K-5 by linarith only [hc.K_large]) (show 0 ≤ E2 d ρ K t by linarith only [he])
  nlinarith only [hh,he,hn]

/-- Availability propagation with the duplicate correction charged to the
    same two-degree error envelope. -/
theorem availability_box_step {H : Finset (Finset α)}
    {I : Finset α} {w : α} (hw : w ∈ available H I)
    {V d ρ K t : ℝ} {C : ℕ} (hc : Conditions V d ρ K t C)
    (hQactual : |((available H I).card:ℝ)-Q V t| ≤ EQ V ρ K t)
    (hdegree : |((incident H I 2 w).card:ℝ)-F2 d t| ≤ E2 d ρ K t)
    (hE : duplicateExcess H I w ≤ C) :
    |((available H (insert w I)).card:ℝ)-Q V (t+d/V)| ≤ EQ V ρ K (t+d/V) := by
  have hh := available_card_step hw
  have hhR : ((available H (insert w I)).card:ℝ)+1+(closes H I w).card = (available H I).card := by
    exact_mod_cast hh
  have hdR : ((incident H I 2 w).card:ℝ) = (closes H I w).card+(duplicateExcess H I w:ℝ) := by
    exact_mod_cast incident_card_eq_closes_add_excess hw
  have hER : (duplicateExcess H I w:ℝ) ≤ E2 d ρ K t := by
    have hh : (duplicateExcess H I w:ℝ) ≤ C := by exact_mod_cast hE
    linarith only [hh,hc.common_small]
  have he : ((available H (insert w I)).card:ℝ)-Q V (t+d/V) =
      ((((available H I).card:ℝ)-Q V t)-(((incident H I 2 w).card:ℝ)-F2 d t))-
        (Q V (t+d/V)-Q V t+F2 d t)-1+(duplicateExcess H I w:ℝ) := by linarith only [hhR,hdR]
  rw [he]
  have hab := abs_sub (((available H I).card:ℝ)-Q V t) (((incident H I 2 w).card:ℝ)-F2 d t)
  have habc := abs_sub
    ((((available H I).card:ℝ)-Q V t)-(((incident H I 2 w).card:ℝ)-F2 d t))
    (Q V (t+d/V)-Q V t+F2 d t)
  have habc1 := abs_sub
    (((((available H I).card:ℝ)-Q V t)-(((incident H I 2 w).card:ℝ)-F2 d t))-
      (Q V (t+d/V)-Q V t+F2 d t)) (1:ℝ)
  have hall := abs_add_le
    (((((available H I).card:ℝ)-Q V t)-(((incident H I 2 w).card:ℝ)-F2 d t))-
      (Q V (t+d/V)-Q V t+F2 d t)-1) (duplicateExcess H I w:ℝ)
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ duplicateExcess H I w)] at hall
  norm_num only [abs_one] at habc1
  linarith only [hab,habc,habc1,hall,hQactual,hdegree,hER,availability_remainder hc,availability_growth hc]

/-- Six actual safe-choice drift signs for the explicit physical profiles.
    The original hypergraph has edge size at most four; nonlinear errors are explicit. -/
theorem signed_drifts {H : Finset (Finset α)} 
    (hfour : ∀ e ∈ H, e.card ≤ 4) (I : Finset α)
    {V d ρ K t : ℝ} {C : ℕ} (hc : Conditions V d ρ K t C)
    (hQactual : |((available H I).card:ℝ)-Q V t| ≤ EQ V ρ K t)
    (h2 : ∀ u ∈ available H I, |((incident H I 2 u).card:ℝ)-F2 d t| ≤ E2 d ρ K t)
    (h3 : ∀ u ∈ available H I, |((incident H I 3 u).card:ℝ)-F3 d t| ≤ E3 d ρ K t)
    (h4 : ∀ u ∈ available H I, |((incident H I 4 u).card:ℝ)-F4 d t| ≤ E4 d ρ K t)
    (hC : ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C)
    (hE : ∀ u ∈ available H I, duplicateExcess H I u ≤ C)
    (hP2 : ∀ u ∈ available H I, (GreedyCodegreeDrift.promotionDefect H I 2 u:ℝ) ≤
      (d*q t)*E2 d ρ K t)
    (hP3 : ∀ u ∈ available H I, (GreedyCodegreeDrift.promotionDefect H I 3 u:ℝ) ≤
      (d*q t)^2*E2 d ρ K t)
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
  apply GreedyCodegreeOneStepProfiles.three_drift_signs hfour I (d*q t) (E2 d ρ K t) t (Q V t) (d/V)
    (EQ V ρ K t) K C C (by positivity) he ht (by dsimp [Q]; positivity)
    (div_pos hd hV) hEQ (by positivity)
    (by linarith only [hc.common_small]) hc.balanced hc.common_small hc.K_large hscale (budget_identity hV)
    hc.Q_small (by simpa only [hf.1] using hc.Q_dominates) hQactual
    (by simpa only [hf.1] using h2)
    (by simpa only [hf.2.1,heq.1] using h3)
    (by simpa only [hf.2.2,heq.2] using h4) hC
    (fun u hu => by exact_mod_cast hE u hu) hP2 hP3
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

#print axioms availability_growth
#print axioms availability_box_step
#print axioms signed_drifts
end
end Erdos773.GreedyCodegreePhysicalStep
