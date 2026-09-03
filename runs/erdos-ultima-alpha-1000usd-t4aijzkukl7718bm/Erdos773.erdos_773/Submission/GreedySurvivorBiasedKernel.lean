import Submission.FiniteKernelSizeBias
import Submission.GreedyAvailableMeanDrift
import Submission.GreedyFiniteKernel

/-!
A different, survivor-biased greedy kernel. It samples a legal vertex with
weight equal to the number of available vertices AFTER that choice. The
weighted actual-mean identities become exact conditional drifts. This file
does not transfer the old uniform-process tail law to the new process and
does not assert a long running time.
-/
namespace Erdos773.GreedySurvivorBiasedKernel
open Finset GreedyHypergraphState StoppedGreedyMoments FiniteKernelCrossing
open FiniteKernelSizeBias GreedyAvailableMeanDrift FiniteMovingMean
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev volume (H : Finset (Finset α)) (I : Finset α) : ℝ := (available H I).card

def nextVolume (H : Finset (Finset α)) (I : Finset α) : ℝ :=
  ∑ v ∈ available H I, volume H (insert v I)

def death (H : Finset (Finset α)) (I : Finset α) (v : α) : ℝ :=
  1+(closes H I v).card

def meanDeath (H : Finset (Finset α)) (I : Finset α) : ℝ :=
  mean (available H I) (death H I)

def deathVariance (H : Finset (Finset α)) (I : Finset α) : ℝ :=
  mean (available H I) (fun v => (death H I v-meanDeath H I)^2)

def kernel (H : Finset (Finset α)) (L : ℕ) : Kernel (Finset α) :=
  tilt (GreedyFiniteKernel.kernel H L) (volume H) (fun _ => Nat.cast_nonneg _)

lemma volume_step {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) : volume H (insert v I) = volume H I-death H I v := by
  have hh : volume H (insert v I)+1+(closes H I v).card = volume H I := by
    exact_mod_cast available_card_step hv
  unfold death
  linarith only [hh]

lemma base_avg {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I)
    (f : Finset α → ℝ) :
    (GreedyFiniteKernel.kernel H L).avg f I = (∑ v ∈ available H I, f (insert v I))/volume H I := by
  classical
  rw [GreedyFiniteKernel.kernel_avg, step, if_pos hr]

lemma normalizer_eq {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I) :
    (GreedyFiniteKernel.kernel H L).avg (volume H) I = nextVolume H I/volume H I := base_avg hr _

lemma normalizer_pos {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I)
    (hs : 0 < nextVolume H I) : 0 < (GreedyFiniteKernel.kernel H L).avg (volume H) I := by
  rw [normalizer_eq hr]
  exact div_pos hs (by exact_mod_cast card_pos.mpr hr.2)

/-- Exact finite weighted-action average. Empty-destination choices carry no
mass when a nonempty destination is possible. -/
theorem avg_ready {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I)
    (hs : 0 < nextVolume H I) (f : Finset α → ℝ) :
    (kernel H L).avg f I =
      (∑ v ∈ available H I, volume H (insert v I)*f (insert v I))/nextVolume H I := by
  rw [kernel, avg_tilt _ _ _ _ _ (normalizer_pos hr hs), base_avg hr, normalizer_eq hr]
  have hQ : volume H I ≠ 0 := by exact_mod_cast (card_pos.mpr hr.2).ne'
  field_simp

/-- Every transition of the biased kernel is a transition of the original
legal greedy kernel, including the zero-normalizer fallback. -/
theorem support_original {H : Finset (Finset α)} {I J : Finset α} {L : ℕ}
    (hJ : 0 < (kernel H L).weight I J) : 0 < (GreedyFiniteKernel.kernel H L).weight I J := by
  classical
  by_cases hZ : 0 < (GreedyFiniteKernel.kernel H L).avg (volume H) I
  · exact ((support_tilt _ _ _ I J hZ).mp hJ).1
  · simpa only [kernel, tilt, if_neg hZ] using hJ

/-- The favorable double variance in the mean two-degree is now an EXACT
conditional drift under this explicitly changed sampling law. -/
theorem mean_two_drift {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I)
    (hs : 0 < nextVolume H I) :
    (kernel H L).avg (fun J => meanDegree H J 2-meanDegree H I 2) I =
      (volume H I*(2*meanDegree H I 3-(meanDegree H I 2)^2)-2*covariance H I 2 2+
        (∑ u ∈ available H I, GreedyTwoDegreeEnergy.correction H I u)+
        (∑ u ∈ available H I, (duplicateExcess H I u:ℝ)*
          (localDegree H I 2 u-meanDegree H I 2)))/nextVolume H I := by
  rw [avg_ready hr hs, weighted_two_mean]

/-- Mixed higher-degree covariance remains explicit and has no imposed sign. -/
theorem mean_higher_drift {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I)
    (hs : 0 < nextVolume H I) (j : ℕ) (hj : 1 ≤ j) :
    (kernel H L).avg (fun J => meanDegree H J j-meanDegree H I j) I =
      (volume H I*((j:ℝ)*meanDegree H I (j+1)-(j-1:ℕ)*meanDegree H I j*meanDegree H I 2)-
        (j:ℝ)*covariance H I j 2+
        (∑ u ∈ available H I, GreedyHigherDegreeEnergy.correction H I j u)+
        (∑ u ∈ available H I, (duplicateExcess H I u:ℝ)*
          (localDegree H I j u-meanDegree H I j)))/nextVolume H I := by
  rw [avg_ready hr hs, weighted_higher_mean H I j hj]

lemma normalizer_mean_death {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I) :
    (GreedyFiniteKernel.kernel H L).avg (volume H) I = volume H I-meanDeath H I := by
  rw [base_avg hr, sum_congr rfl (fun v hv => volume_step hv), sum_sub_distrib, sum_const, nsmul_eq_mul]
  unfold meanDeath mean
  have hQ : volume H I ≠ 0 := by exact_mod_cast (card_pos.mpr hr.2).ne'
  change (volume H I*volume H I-(∑ v ∈ available H I, death H I v))/volume H I = _
  field_simp

lemma base_volume_variance {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I) :
    (GreedyFiniteKernel.kernel H L).avg
      (fun J => (volume H J-(GreedyFiniteKernel.kernel H L).avg (volume H) I)^2) I = deathVariance H I := by
  rw [base_avg hr]
  change _ = (∑ v ∈ available H I, (death H I v-meanDeath H I)^2)/volume H I
  congr 1
  apply sum_congr rfl
  intro v hv
  rw [volume_step hv, normalizer_mean_death hr]
  ring

/-- Actual availability loss is improved by the variance of closure sizes.
This does not assert that that improvement controls the higher means. -/
theorem availability_drift {H : Finset (Finset α)} {I : Finset α} {L : ℕ} (hr : Ready H L I)
    (hs : 0 < nextVolume H I) :
    (kernel H L).avg (fun J => volume H J-volume H I) I =
      -meanDeath H I+deathVariance H I/(volume H I-meanDeath H I) := by
  rw [kernel, tilt_decrement _ _ _ _ _ (normalizer_pos hr hs), base_volume_variance hr,
    normalizer_mean_death hr]
  ring

#print axioms avg_ready
#print axioms support_original
#print axioms mean_two_drift
#print axioms mean_higher_drift
#print axioms normalizer_mean_death
#print axioms availability_drift
end
end Erdos773.GreedySurvivorBiasedKernel
