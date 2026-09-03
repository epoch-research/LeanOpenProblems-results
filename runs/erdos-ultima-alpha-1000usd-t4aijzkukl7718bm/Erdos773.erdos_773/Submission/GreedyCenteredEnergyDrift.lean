import Submission.FiniteCenteredPowerDeaths
import Submission.FiniteCenteredStationarity
import Submission.GreedyAvailableMeanDrift
import Submission.GreedyFiniteKernel

/-!
An actual one-step drift bound for the optimized even-power degree energy
of the UNIFORM greedy process. Centers are chosen anew at each state; a
proposed next center is used only as an upper comparison. All killed-vertex
energy is retained, as are the actual safe-choice variances.
-/
namespace Erdos773.GreedyCenteredEnergyDrift
open Finset GreedyHypergraphState GreedyLinearLocal GreedyProfileDrift
open GreedyAvailableMeanDrift FiniteCenteredPower GreedySurvivalTotalDrift
open FiniteKernelCrossing StoppedGreedyMoments
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def degreeCenter (H : Finset (Finset α)) (I : Finset α) (j p : ℕ) : ℝ :=
  center (available H I) (localDegree H I j) p

def degreeEnergy (H : Finset (Finset α)) (I : Finset α) (j p : ℕ) : ℝ :=
  energy (available H I) (localDegree H I j) p

def error (H : Finset (Finset α)) (I : Finset α) (j p : ℕ) (u : α) : ℝ :=
  localDegree H I j u-degreeCenter H I j p

def shiftedVariance (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (μ : ℝ) (u : α) : ℝ :=
  ∑ v ∈ safeChoices H I u, (localDegree H (insert v I) j u-localDegree H I j u-μ)^2

/-- Center shifting charges the actual raw second moment and the square of
that shift, not a worst-case increment squared on every choice. -/
theorem shiftedVariance_le (H : Finset (Finset α)) (I : Finset α) (j : ℕ)
    (μ : ℝ) (u : α) (V : ℝ)
    (hV : (∑ v ∈ safeChoices H I u,
      (localDegree H (insert v I) j u-localDegree H I j u)^2) ≤ V) :
    shiftedVariance H I j μ u ≤ 2*V+2*(available H I).card*μ^2 := by
  have hh : shiftedVariance H I j μ u ≤
      2*(∑ v ∈ safeChoices H I u, (localDegree H (insert v I) j u-localDegree H I j u)^2)+
        (safeChoices H I u).card*(2*μ^2) := by
    unfold shiftedVariance
    calc
      _ ≤ ∑ v ∈ safeChoices H I u,
          (2*(localDegree H (insert v I) j u-localDegree H I j u)^2+2*μ^2) := by
        apply sum_le_sum
        intro v hv
        nlinarith only [sq_nonneg (localDegree H (insert v I) j u-localDegree H I j u+μ)]
      _ = _ := by rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  have hc : ((safeChoices H I u).card:ℝ) ≤ (available H I).card := by
    exact_mod_cast card_le_card (filter_subset (fun v => u ∈ available H (insert v I)) (available H I))
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2*μ^2 by positivity)
  nlinarith only [hh, hm, hV]

/-- The safe-choice factor on a center shift is retained exactly. For a
proposed profile numerator F, the missing choices produce this extra term. -/
theorem profile_shift (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (F : ℝ)
    {u : α} (hu : u ∈ available H I) :
    survivalDrift H I j u-(safeChoices H I u).card*(F/(available H I).card) =
      survivalDrift H I j u-F+(1+((closes H I u).card:ℝ))*F/(available H I).card := by
  have hc := available_card_step hu
  rw [← safeChoices_eq_available hu] at hc
  have hc' : ((safeChoices H I u).card:ℝ)+1+(closes H I u).card = (available H I).card := by
    exact_mod_cast hc
  have hQ : ((available H I).card:ℝ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr (show (available H I).Nonempty from ⟨u,hu⟩)).ne'
  have hm := congrArg (fun z : ℝ => z*F) hc'
  field_simp
  nlinarith only [hm]

/-- Sum of actual energy increments, with a chosen common center shift μ.
The right side retains signed survival drift, quadratic variation, and all
death energy. No regularity or linearity hypothesis is hidden here. -/
theorem sum_drift (H : Finset (Finset α)) (I : Finset α) (j n : ℕ)
    (hn : Even (n+2)) (μ : ℝ) (B : α → ℝ)
    (hB : ∀ u ∈ available H I, ∀ v ∈ safeChoices H I u,
      |localDegree H (insert v I) j u-localDegree H I j u-μ| ≤ B u) :
    (∑ v ∈ available H I, (degreeEnergy H (insert v I) j (n+2)-degreeEnergy H I j (n+2))) ≤
      (n+2:ℕ)*(∑ u ∈ available H I, (error H I j (n+2) u)^(n+1)*
        (survivalDrift H I j u-(safeChoices H I u).card*μ))+
      FinitePowerTaylor.coefficient n*(∑ u ∈ available H I,
        (|error H I j (n+2) u|^n+(B u)^n)*shiftedVariance H I j μ u)-
      (∑ u ∈ available H I, (1+((closes H I u).card:ℝ))*|error H I j (n+2) u|^(n+2)) := by
  let S := available H I
  let T := fun v => available H (insert v I)
  have hT (v : α) (_hv : v ∈ S) : T v ⊆ S := available_antitone (subset_insert v I)
  let F := fun v u =>
    (n+2:ℕ)*(error H I j (n+2) u)^(n+1)*(localDegree H (insert v I) j u-localDegree H I j u-μ)+
    FinitePowerTaylor.coefficient n*(|error H I j (n+2) u|^n+(B u)^n)*
      (localDegree H (insert v I) j u-localDegree H I j u-μ)^2
  have hp (v : α) (hv : v ∈ S) :
      degreeEnergy H (insert v I) j (n+2)-degreeEnergy H I j (n+2) ≤
        (∑ u ∈ T v, F v u)-(∑ u ∈ S \ T v, |error H I j (n+2) u|^(n+2)) := by
    have he (u : α) :
        (localDegree H (insert v I) j u-(degreeCenter H I j (n+2)+μ))-
          (localDegree H I j u-degreeCenter H I j (n+2)) =
        localDegree H (insert v I) j u-localDegree H I j u-μ := by ring
    have hinc (u : α) (hu : u ∈ T v) :
        |(localDegree H (insert v I) j u-(degreeCenter H I j (n+2)+μ))-
          (localDegree H I j u-center S (localDegree H I j) (n+2))| ≤ B u := by
      change |(localDegree H (insert v I) j u-(degreeCenter H I j (n+2)+μ))-
        (localDegree H I j u-degreeCenter H I j (n+2))| ≤ B u
      rw [he]
      exact hB u (hT v hv hu) v (mem_filter.mpr ⟨hv, hu⟩)
    have hh := FiniteCenteredPowerDeaths.survivor_taylor (hT v hv)
      (localDegree H I j) (localDegree H (insert v I) j) n hn (degreeCenter H I j (n+2)+μ) B hinc
    change degreeEnergy H (insert v I) j (n+2)-degreeEnergy H I j (n+2) ≤ _ at hh
    change _ ≤ (∑ u ∈ T v, F v u)-_ 
    convert hh using 1
    apply congrArg (fun z => z-(∑ u ∈ S \ T v, |error H I j (n+2) u|^(n+2)))
    apply sum_congr rfl
    intro u hu
    change F v u = _
    dsimp only [F, error, degreeCenter, S]
    ring
  have hh := sum_le_sum hp
  simp only [sum_sub_distrib] at hh
  rw [survivor_sum S T hT, FiniteCenteredPowerDeaths.death_sum S T hT] at hh
  have hfirst (u : α) :
      (∑ v ∈ S.filter (fun v => u ∈ T v), F v u) =
      (n+2:ℕ)*(error H I j (n+2) u)^(n+1)*(survivalDrift H I j u-(safeChoices H I u).card*μ)+
      FinitePowerTaylor.coefficient n*(|error H I j (n+2) u|^n+(B u)^n)*shiftedVariance H I j μ u := by
    change (∑ v ∈ safeChoices H I u, F v u) = _
    dsimp only [F]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
    rfl
  have hdeath (u : α) (hu : u ∈ S) :
      (S.card:ℝ)-(S.filter (fun v => u ∈ T v)).card = 1+(closes H I u).card := by
    have hc := available_card_step hu
    rw [← safeChoices_eq_available hu] at hc
    have hc' : ((safeChoices H I u).card:ℝ)+1+(closes H I u).card = S.card := by exact_mod_cast hc
    change (S.card:ℝ)-(safeChoices H I u).card = _
    linarith only [hc']
  rw [sum_congr rfl (fun u _ => hfirst u), sum_add_distrib] at hh
  simp_rw [mul_assoc] at hh
  rw [← mul_sum, ← mul_sum] at hh
  have he : (∑ u ∈ S, ((S.card:ℝ)-(S.filter (fun v => u ∈ T v)).card)*|error H I j (n+2) u|^(n+2)) =
      ∑ u ∈ S, (1+((closes H I u).card:ℝ))*|error H I j (n+2) u|^(n+2) :=
    sum_congr rfl (fun u hu => by rw [hdeath u hu])
  rw [he] at hh
  simpa only [sum_sub_distrib] using hh

/-- Genuine uniform conditional energy drift. The center at the destination
is optimized there, rather than frozen or differentiated. -/
theorem uniform_drift (H : Finset (Finset α)) (I : Finset α) (L j n : ℕ)
    (hr : Ready H L I) (hn : Even (n+2)) (μ : ℝ) (B : α → ℝ)
    (hB : ∀ u ∈ available H I, ∀ v ∈ safeChoices H I u,
      |localDegree H (insert v I) j u-localDegree H I j u-μ| ≤ B u) :
    (GreedyFiniteKernel.kernel H L).avg
      (fun J => degreeEnergy H J j (n+2)-degreeEnergy H I j (n+2)) I ≤
      ((n+2:ℕ)*(∑ u ∈ available H I, (error H I j (n+2) u)^(n+1)*
        (survivalDrift H I j u-(safeChoices H I u).card*μ))+
      FinitePowerTaylor.coefficient n*(∑ u ∈ available H I,
        (|error H I j (n+2) u|^n+(B u)^n)*shiftedVariance H I j μ u)-
      (∑ u ∈ available H I, (1+((closes H I u).card:ℝ))*|error H I j (n+2) u|^(n+2)))/
        (available H I).card := by
  classical
  rw [GreedyFiniteKernel.kernel_avg, step, if_pos hr]
  exact div_le_div_of_nonneg_right (sum_drift H I j n hn μ B hB) (Nat.cast_nonneg _)

/-- Stationarity cancels any common profile numerator WITHOUT moving the
comparison center. Consequently there is no artificial μ² variance cost. -/
theorem uniform_drift_stationary (H : Finset (Finset α)) (I : Finset α) (L j n : ℕ)
    (hr : Ready H L I) (hn : Even (n+2)) (F : ℝ) (B : α → ℝ)
    (hB : ∀ u ∈ available H I, ∀ v ∈ safeChoices H I u,
      |localDegree H (insert v I) j u-localDegree H I j u| ≤ B u) :
    (GreedyFiniteKernel.kernel H L).avg
      (fun J => degreeEnergy H J j (n+2)-degreeEnergy H I j (n+2)) I ≤
      ((n+2:ℕ)*(∑ u ∈ available H I, (error H I j (n+2) u)^(n+1)*
        (survivalDrift H I j u-F))+
      FinitePowerTaylor.coefficient n*(∑ u ∈ available H I,
        (|error H I j (n+2) u|^n+(B u)^n)*shiftedVariance H I j 0 u)-
      (∑ u ∈ available H I, (1+((closes H I u).card:ℝ))*|error H I j (n+2) u|^(n+2)))/
        (available H I).card := by
  have hh := uniform_drift H I L j n hr hn 0 B (by simpa only [sub_zero] using hB)
  simp only [mul_zero, sub_zero] at hh
  have he := FiniteCenteredStationarity.constant_cancel (available H I) (localDegree H I j)
    (survivalDrift H I j) n hn F
  change (∑ u ∈ available H I, (error H I j (n+2) u)^(n+1)*(survivalDrift H I j u-F)) =
    (∑ u ∈ available H I, (error H I j (n+2) u)^(n+1)*survivalDrift H I j u) at he
  rwa [← he] at hh

/-- A usable conditional-energy certificate: supply the signed operator
budget, the RAW local second moments, and a lower death hazard. All three
are hypotheses, not presumed trajectory estimates. -/
theorem uniform_drift_bound (H : Finset (Finset α)) (I : Finset α) (L j n : ℕ)
    (hr : Ready H L I) (hn : Even (n+2)) (F D l : ℝ) (B V : α → ℝ)
    (hB0 : ∀ u ∈ available H I, 0 ≤ B u)
    (hB : ∀ u ∈ available H I, ∀ v ∈ safeChoices H I u,
      |localDegree H (insert v I) j u-localDegree H I j u| ≤ B u)
    (hD : (∑ u ∈ available H I, (error H I j (n+2) u)^(n+1)*
      (survivalDrift H I j u-F)) ≤ D)
    (hV : ∀ u ∈ available H I, (∑ v ∈ safeChoices H I u,
      (localDegree H (insert v I) j u-localDegree H I j u)^2) ≤ V u)
    (hl : ∀ u ∈ available H I, l ≤ 1+((closes H I u).card:ℝ)) :
    (GreedyFiniteKernel.kernel H L).avg
      (fun J => degreeEnergy H J j (n+2)-degreeEnergy H I j (n+2)) I ≤
      ((n+2:ℕ)*D+FinitePowerTaylor.coefficient n*(∑ u ∈ available H I,
        (|error H I j (n+2) u|^n+(B u)^n)*V u)-l*degreeEnergy H I j (n+2))/(available H I).card := by
  apply (uniform_drift_stationary H I L j n hr hn F B hB).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hd := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg (α := ℝ) (n+2))
  have hv : (∑ u ∈ available H I, (|error H I j (n+2) u|^n+(B u)^n)*shiftedVariance H I j 0 u) ≤
      ∑ u ∈ available H I, (|error H I j (n+2) u|^n+(B u)^n)*V u := by
    apply sum_le_sum
    intro u hu
    apply mul_le_mul_of_nonneg_left _ (add_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (hB0 u hu) _))
    simpa only [shiftedVariance, sub_zero] using hV u hu
  have hv' := mul_le_mul_of_nonneg_left hv (FinitePowerTaylor.coefficient_nonneg n)
  have hdeath := sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (hl u hu)
    (pow_nonneg (abs_nonneg (error H I j (n+2) u)) (n+2)))
  rw [← mul_sum] at hdeath
  change l*degreeEnergy H I j (n+2) ≤ _ at hdeath
  linarith only [hd, hv', hdeath]

#print axioms shiftedVariance_le
#print axioms profile_shift
#print axioms sum_drift
#print axioms uniform_drift
#print axioms uniform_drift_stationary
#print axioms uniform_drift_bound
end
end Erdos773.GreedyCenteredEnergyDrift
