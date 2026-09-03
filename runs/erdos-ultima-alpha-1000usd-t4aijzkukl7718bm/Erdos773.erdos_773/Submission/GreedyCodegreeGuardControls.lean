import Submission.GreedyGuardControls
import Submission.GreedyCodegreeProfileGuard
import Submission.GreedyCodegreeMomentControl

/-!
Actual concentration controls for the concrete profile guard. Drift is
fully discharged using the physical estimates. The remaining numerical
input is a uniform total increment cap, and the variance is explicit.
-/
namespace Erdos773.GreedyCodegreeGuardControls
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyLinearDrift GreedyLinearLocal
open GreedyTrackedState GreedyTrackedMoments GreedyProfileRecords GreedyProfileGuard GreedyCodegreeProfileGuard
open GreedyProfileDrift GreedyCodegreeMomentControl GreedyRecordedCrossing
open GreedyGuardControls FourUniformRegularization GreedyCodegreeDrift
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The extra scalar requirements for the two nonlinear promotion guards. -/
def PromotionBounds (p : Parameters) (T B2 B3 : ℕ) : Prop :=
  ∀ n < T, (B2:ℝ) ≤ (p.d*q (time p n))*E2 p.d p.rho p.K (time p n) ∧
    (B3:ℝ) ≤ (p.d*q (time p n))^2*E2 p.d p.rho p.K (time p n)

def rawCap (p : Parameters) (k C : ℕ) (j : Fin 3) (n : ℕ) : ℝ :=
  ![(k:ℝ)+C+C,(k:ℝ)*(upper p 0 n+1),(k:ℝ)*(upper p 0 n+1)] j

def rawVariance (p : Parameters) (k C : ℕ) (j : Fin 3) (n : ℕ) : ℝ :=
  ![((k:ℝ)+C+C)*(2*upper p 1 n+(upper p 0 n)^2),
    (k:ℝ)*(upper p 0 n+1)*(3*upper p 2 n+2*(upper p 0 n+1)*upper p 1 n),
    (k:ℝ)*(upper p 0 n+1)*(3*(upper p 0 n+1)*upper p 2 n)] j

def variance (p : Parameters) (k C : ℕ) (j : Fin 3) (lower : Bool) (n : ℕ) : ℝ :=
  2*(rawVariance p k C j n/qmin p n)+2*(signedProfile p j lower (n+1)-signedProfile p j lower n)^2

lemma guard_Q_lower {p : Parameters} {H : Finset (Finset α)} {L T C B2 B3 n : ℕ}
    {s : Tracked H T} (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s) :
    qmin p n ≤ ((available H s.chosen).card:ℝ) := by
  have hh := (abs_le.mp hg.2.1).1
  dsimp [qmin]
  linarith only [hh]

lemma guard_degree_upper {p : Parameters} {H : Finset (Finset α)} {L T C B2 B3 n : ℕ}
    {τ : ℝ} (hh : Horizon p L T C τ) (hn : n ≤ T)
    {s : Tracked H T} (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s) (j : Fin 3) (u : α) :
    ((incident H s.chosen (j.val+2) u).card:ℝ) ≤ upper p j n := by
  by_cases hu : u ∈ available H s.chosen
  · have hh := (abs_le.mp (hg.2.2.1 j u hu)).2
    dsimp [upper]
    linarith only [hh]
  · rw [incident_eq_empty_of_unavailable hu,card_empty,Nat.cast_zero]
    exact upper_nonneg hh hn j

/-- The concrete guard implies all required moment hypotheses. -/
theorem moment_control {p : Parameters} {H : Finset (Finset α)} (k : ℕ)
    (hk : ∀ a b : α, a ≠ b → pairDegree H a b ≤ k)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C B2 B3 : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (j : Fin 3) (u : α) (lower : Bool) (b : ℝ)
    (hcap : ∀ n < T, rawCap p k C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b) :
    MomentControl H L T (GreedyCodegreeProfileGuard.guard p H L T C B2 B3) (signedProfile p j lower) j u (sign lower) b
      (rawCap p k C j) (variance p k C j lower) := by
  have hv (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s) := hg.1
  have hQ (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s) := guard_Q_lower hg
  have h2 (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s)
      (x : α) (_hx : x ∈ available H s.chosen) := guard_degree_upper hh hn.le hg 0 x
  have hl (j : Fin 3) (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s) :=
    guard_degree_upper hh hn.le hg j u
  have h3 (n : ℕ) (hn : n < T) (s : Tracked H T) (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s)
      (_hu : u ∈ available H s.chosen) := hl 1 n hn s hg
  have hC (n : ℕ) (_hn : n < T) (s : Tracked H T) (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s) := hg.2.2.2.1
  have hE (n : ℕ) (_hn : n < T) (s : Tracked H T)
      (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s) := hg.2.2.2.2.1
  have h5 (n : ℕ) (_hn : n < T) (s : Tracked H T) (_hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s) :
      ((incident H s.chosen 5 u).card:ℝ) ≤ 0 := by
    rw [incident_eq_empty_of_size 4 hfour s.chosen 5 (by omega) u]
    norm_num
  fin_cases j
  · exact GreedyCodegreeMomentControl.two_moment_control k hk L T _ _ u _ b (sign_abs lower)
      (upper p 0) (upper p 1) (qmin p) (fun _ => C) (fun _ => C)
      (fun n hn => upper_nonneg hh hn.le 0) (fun n hn => upper_nonneg hh hn.le 1)
      (fun n hn => qmin_pos hh hn.le) hcap hv hQ h2 h3 hC hE
  · exact GreedyCodegreeMomentControl.higher_moment_control k hk L T _ _ 1 (by decide) u _ b (sign_abs lower)
      (upper p 0) (upper p 1) (upper p 2) (qmin p)
      (fun n hn => upper_nonneg hh hn.le 0) (fun n hn => upper_nonneg hh hn.le 1)
      (fun n hn => upper_nonneg hh hn.le 2) (fun n hn => qmin_pos hh hn.le)
      hcap hv hQ h2 (hl 1) (hl 2)
  · have hc := GreedyCodegreeMomentControl.higher_moment_control k hk L T (GreedyCodegreeProfileGuard.guard p H L T C B2 B3) (signedProfile p 2 lower)
      2 (by decide) u _ b (sign_abs lower) (upper p 0) (upper p 2) (fun _ => 0) (qmin p)
      (fun n hn => upper_nonneg hh hn.le 0) (fun n hn => upper_nonneg hh hn.le 2)
      (fun _ _ => le_rfl) (fun n hn => qmin_pos hh hn.le) hcap hv hQ h2 (hl 2) h5
    convert hc using 1
    funext n
    simp [variance,rawVariance]

/-- All signed drift obligations for the guard are now proved, rather than
    included as assumptions in the concentration control. -/
theorem guard_signed_drift {p : Parameters} {H : Finset (Finset α)}
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C B2 B3 n : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (hprom : PromotionBounds p T B2 B3) (hn : n < T) (s : Tracked H T) (hg : GreedyCodegreeProfileGuard.guard p H L T C B2 B3 n s)
    (j : Fin 3) (u : α) (lower : Bool) :
    sign lower*(survivalDrift H s.chosen (j.val+2) u-
      (safeChoices H s.chosen u).card*(signedProfile p j lower (n+1)-signedProfile p j lower n)) ≤ 0 := by
  have hP2 (u : α) (hu : u ∈ available H s.chosen) :
      (promotionDefect H s.chosen 2 u:ℝ) ≤ (p.d*q (time p n))*E2 p.d p.rho p.K (time p n) :=
    (show (promotionDefect H s.chosen 2 u:ℝ) ≤ B2 by exact_mod_cast hg.2.2.2.2.2.1 u hu).trans (hprom n hn).1
  have hP3 (u : α) (hu : u ∈ available H s.chosen) :
      (promotionDefect H s.chosen 3 u:ℝ) ≤ (p.d*q (time p n))^2*E2 p.d p.rho p.K (time p n) :=
    (show (promotionDefect H s.chosen 3 u:ℝ) ≤ B3 by exact_mod_cast hg.2.2.2.2.2.2 u hu).trans (hprom n hn).2
  have hd := GreedyCodegreePhysicalStep.signed_drifts hfour s.chosen (hh.conditions hn.le) hg.2.1
    (hg.2.2.1 0) (hg.2.2.1 1) (hg.2.2.1 2) hg.2.2.2.1 hg.2.2.2.2.1 hP2 hP3 u
  fin_cases j <;> cases lower <;> dsimp [signedProfile,center,width,profile,envelope,sign]
    <;> rw [time_step] <;> nlinarith only [hd.1.1,hd.1.2,hd.2.1.1,hd.2.1.2,hd.2.2.1,hd.2.2.2]

theorem control {p : Parameters} {H : Finset (Finset α)} (k : ℕ)
    (hk : ∀ a b : α, a ≠ b → pairDegree H a b ≤ k)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C B2 B3 : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (hprom : PromotionBounds p T B2 B3) (j : Fin 3) (u : α) (lower : Bool) (b : ℝ)
    (hcap : ∀ n < T, rawCap p k C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b) :
    Control H L T (GreedyCodegreeProfileGuard.guard p H L T C B2 B3) (signedProfile p j lower) j u (sign lower) b
      (rawCap p k C j) (variance p k C j lower) := by
  refine ⟨moment_control k hk hfour hh j u lower b hcap,?_⟩
  intro n hn s hr hrun hg
  exact guard_signed_drift hfour hh hprom hn s hg j u lower

#print axioms moment_control
#print axioms guard_signed_drift
#print axioms control
end
end Erdos773.GreedyCodegreeGuardControls
