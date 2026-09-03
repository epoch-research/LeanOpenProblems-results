import Submission.GreedyProfileGuard
import Submission.GreedyProfileVariance

/-!
Actual concentration controls for the concrete profile guard. Drift is
fully discharged using the physical estimates. The remaining numerical
input is a uniform total increment cap, and the variance is explicit.
-/
namespace Erdos773.GreedyGuardControls
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyLinearDrift GreedyLinearLocal
open GreedyTrackedState GreedyTrackedMoments GreedyProfileRecords GreedyProfileGuard
open GreedyProfileDrift GreedyProfileVariance GreedyRecordedCrossing
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus GreedyPhysicalStep
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def upper (p : Parameters) (j : Fin 3) (n : ℕ) : ℝ := center p j n+width p j n
def qmin (p : Parameters) (n : ℕ) : ℝ := Q p.V (time p n)-EQ p.V p.rho p.K (time p n)

def rawCap (p : Parameters) (C : ℕ) (j : Fin 3) (n : ℕ) : ℝ :=
  ![(C:ℝ)+1,upper p 0 n+1,upper p 0 n+1] j

def rawVariance (p : Parameters) (C : ℕ) (j : Fin 3) (n : ℕ) : ℝ :=
  ![((C:ℝ)+1)*(2*upper p 1 n+(upper p 0 n)^2),
    (upper p 0 n+1)*(3*upper p 2 n+2*(upper p 0 n+1)*upper p 1 n),
    (upper p 0 n+1)*(3*(upper p 0 n+1)*upper p 2 n)] j

def variance (p : Parameters) (C : ℕ) (j : Fin 3) (lower : Bool) (n : ℕ) : ℝ :=
  2*(rawVariance p C j n/qmin p n)+2*(signedProfile p j lower (n+1)-signedProfile p j lower n)^2

lemma upper_nonneg {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) (j : Fin 3) : 0 ≤ upper p j n := by
  have hc := hh.conditions hn
  exact add_nonneg (profile_nonneg hc.d_pos.le hc.time_nonneg j)
    (envelope_nonneg hc.d_pos.le hc.rho_nonneg j _)

lemma qmin_pos {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) : 0 < qmin p n := by
  have hc := hh.conditions hn
  have hp : 0 < Q p.V (time p n) := mul_pos hc.V_pos (q_pos _)
  dsimp [qmin]
  linarith only [hc.Q_small,hp]

lemma guard_Q_lower {p : Parameters} {H : Finset (Finset α)} {L T C n : ℕ}
    {s : Tracked H T} (hg : guard p H L T C n s) :
    qmin p n ≤ ((available H s.chosen).card:ℝ) := by
  have hh := (abs_le.mp hg.2.1).1
  dsimp [qmin]
  linarith only [hh]

lemma guard_degree_upper {p : Parameters} {H : Finset (Finset α)} {L T C n : ℕ}
    {τ : ℝ} (hh : Horizon p L T C τ) (hn : n ≤ T)
    {s : Tracked H T} (hg : guard p H L T C n s) (j : Fin 3) (u : α) :
    ((incident H s.chosen (j.val+2) u).card:ℝ) ≤ upper p j n := by
  by_cases hu : u ∈ available H s.chosen
  · have hh := (abs_le.mp (hg.2.2.1 j u hu)).2
    dsimp [upper]
    linarith only [hh]
  · rw [incident_eq_empty_of_unavailable hu,card_empty,Nat.cast_zero]
    exact upper_nonneg hh hn j

/-- The concrete guard implies all required moment hypotheses. -/
theorem moment_control {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (j : Fin 3) (u : α) (lower : Bool) (b : ℝ)
    (hcap : ∀ n < T, rawCap p C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b) :
    MomentControl H L T (guard p H L T C) (signedProfile p j lower) j u (sign lower) b
      (rawCap p C j) (variance p C j lower) := by
  have hv (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : guard p H L T C n s) := hg.1
  have hQ (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : guard p H L T C n s) := guard_Q_lower hg
  have h2 (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : guard p H L T C n s)
      (x : α) (_hx : x ∈ available H s.chosen) := guard_degree_upper hh hn.le hg 0 x
  have hl (j : Fin 3) (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : guard p H L T C n s) :=
    guard_degree_upper hh hn.le hg j u
  have h3 (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : guard p H L T C n s)
      (_hu : u ∈ available H s.chosen) := hl 1 n hn s hg
  have hC (n : ℕ) (_hn : n < T) (s : Tracked H T) (hg : guard p H L T C n s) := hg.2.2.2
  have h5 (n : ℕ) (_hn : n < T) (s : Tracked H T) (_hg : guard p H L T C n s) :
      ((incident H s.chosen 5 u).card:ℝ) ≤ 0 := by
    rw [incident_eq_empty_of_size 4 hfour s.chosen 5 (by omega) u]
    norm_num
  fin_cases j
  · exact two_moment_control hlin L T _ _ u _ b (sign_abs lower)
      (upper p 0) (upper p 1) (qmin p) (fun _ => C)
      (fun n hn => upper_nonneg hh hn.le 0) (fun n hn => upper_nonneg hh hn.le 1)
      (fun n hn => qmin_pos hh hn.le) hcap hv hQ h2 h3 hC
  · exact higher_moment_control hlin L T _ _ 1 (by decide) u _ b (sign_abs lower)
      (upper p 0) (upper p 1) (upper p 2) (qmin p)
      (fun n hn => upper_nonneg hh hn.le 0) (fun n hn => upper_nonneg hh hn.le 1)
      (fun n hn => upper_nonneg hh hn.le 2) (fun n hn => qmin_pos hh hn.le)
      hcap hv hQ h2 (hl 1) (hl 2)
  · have hc := higher_moment_control hlin L T (guard p H L T C) (signedProfile p 2 lower)
      2 (by decide) u _ b (sign_abs lower) (upper p 0) (upper p 2) (fun _ => 0) (qmin p)
      (fun n hn => upper_nonneg hh hn.le 0) (fun n hn => upper_nonneg hh hn.le 2)
      (fun _ _ => le_rfl) (fun n hn => qmin_pos hh hn.le) hcap hv hQ h2 (hl 2) h5
    convert hc using 1
    funext n
    simp [variance,rawVariance]

/-- All signed drift obligations for the guard are now proved, rather than
    included as assumptions in the concentration control. -/
theorem guard_signed_drift {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C n : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (hn : n < T) (s : Tracked H T) (hg : guard p H L T C n s)
    (j : Fin 3) (u : α) (lower : Bool) :
    sign lower*(survivalDrift H s.chosen (j.val+2) u-
      (safeChoices H s.chosen u).card*(signedProfile p j lower (n+1)-signedProfile p j lower n)) ≤ 0 := by
  have hd := signed_drifts hlin hfour s.chosen (hh.conditions hn.le) hg.2.1
    (hg.2.2.1 0) (hg.2.2.1 1) (hg.2.2.1 2) hg.2.2.2 u
  fin_cases j <;> cases lower <;> dsimp [signedProfile,center,width,profile,envelope,sign]
    <;> rw [time_step] <;> nlinarith only [hd.1.1,hd.1.2,hd.2.1.1,hd.2.1.2,hd.2.2.1,hd.2.2.2]

theorem control {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (j : Fin 3) (u : α) (lower : Bool) (b : ℝ)
    (hcap : ∀ n < T, rawCap p C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b) :
    Control H L T (guard p H L T C) (signedProfile p j lower) j u (sign lower) b
      (rawCap p C j) (variance p C j lower) := by
  refine ⟨moment_control hlin hfour hh j u lower b hcap,?_⟩
  intro n hn s hr hrun hg
  exact guard_signed_drift hlin hfour hh hn s hg j u lower

#print axioms moment_control
#print axioms guard_signed_drift
#print axioms control
end
end Erdos773.GreedyGuardControls
