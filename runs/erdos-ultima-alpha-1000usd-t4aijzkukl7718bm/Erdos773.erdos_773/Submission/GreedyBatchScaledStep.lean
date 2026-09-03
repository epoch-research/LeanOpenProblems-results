import Submission.GreedyBatchScaledErrors
import Submission.GreedyBatchDensityStep

/-! The finite density step with every local tail fully instantiated at
shrinking-batch scales. Only deterministic cap, fit, rate and volume
inequalities remain to validate an actual schedule. -/
namespace Erdos773.GreedyBatchScaledStep
open GreedyBatchCertificate GreedyBatchDensityStep GreedyBatchReward
open GreedyBatchScaledErrors GreedyBatchScaleTails
set_option maxHeartbeats 2500000
noncomputable section
universe u

theorem density_step (c c' : Caps) (m V W : ℕ) (p d δ ρ : ℝ)
    (h : Conditions c m p d)
    (hf : Fits c (margins c m p d) p (1/(m:ℝ)^2) c') (hP : c.P≤c'.P)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hρ : 0<ρ)
    (hrate : ρ≤rate c p δ-tests V*GreedyBatchScaleTails.failure m)
    (hW : copies c'*V≤W)
    (hfuture : UniformDensity.{u} (post c') W δ) : UniformDensity.{u} c V ρ := by
  exact GreedyBatchDensityStep.density_step c c' (margins c m p d) p (1/(m:ℝ)^2)
    δ ρ (GreedyBatchScaleTails.failure m) (m^10) V W
    (margins_positive c m p d h) (probability_range c m p d h) hf hP hδ hδ1 hρ
    (by unfold GreedyBatchScaleTails.failure; positivity)
    (vertex_errors c m p d h) (pair_errors c m p d h) hrate hW hfuture

#print axioms density_step
end
end Erdos773.GreedyBatchScaledStep
