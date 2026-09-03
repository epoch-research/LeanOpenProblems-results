import Submission.BernsteinActualBudgetExplore

/-! Quantitative interpretation of the finite variance-sensitive transfer.
No new coarse profile or infinite construction is assumed here. -/
namespace Erdos66BernsteinBudgetParameters
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66CenteredColorSelection
  Erdos66BernsteinColorEnergy Erdos66LogarithmicColorBudget
open scoped Classical
set_option maxHeartbeats 2200000
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

lemma variance_le_mean_range (K : α → α → ℝ) (M : ℝ)
    (h0 : ∀ x y, 0≤K x y) (hM : ∀ x y, K x y≤M) :
    colorVariance K≤M*kernelMean K-(kernelMean K)^2 := by
  have he := mean_mono (fun z : α×α ↦ (K z.1 z.2)^2)
    (fun z ↦ M*K z.1 z.2) (fun z ↦ by
      have hh := mul_le_mul_of_nonneg_right (hM z.1 z.2) (h0 z.1 z.2)
      nlinarith only [hh])
  rw [mean_const_mul] at he
  unfold colorVariance
  rw [kernelVariance_identity]
  exact sub_le_sub_right he _

lemma variance_le_mean_times_range (K : α → α → ℝ) (M : ℝ)
    (h0 : ∀ x y, 0≤K x y) (hM : ∀ x y, K x y≤M) :
    colorVariance K≤M*kernelMean K := by
  have he := variance_le_mean_range K M h0 hM
  nlinarith only [he,sq_nonneg (kernelMean K)]

/-- The exact normalized bound, keeping the variance and range terms apart.
In applications m is twice the number of coarse kernels, to include signs. -/
lemma root_relative_variance_bound (h m : ℕ) (hh : 0<h)
    (μ V M X : ℝ) (hμ : 0<μ)
    (he : (X-(h:ℝ)^2*μ)^2≤
      6*(h:ℝ)*(8*μ^2*(h:ℝ)^2+2*bernsteinEnergy h m V M)) :
    (X-(h:ℝ)^2*μ)^2/((h:ℝ)^2*μ)^2≤
      48/(h:ℝ)+1536*V*listLog h m/((h:ℝ)*μ^2)+
        1536*M^2*(listLog h m)^2/((h:ℝ)^2*μ^2)+24*M^2/((h:ℝ)^2*μ^2) := by
  have hh' : (0:ℝ)<h := by exact_mod_cast hh
  have hb := div_le_div_of_nonneg_right he (sq_nonneg ((h:ℝ)^2*μ))
  refine hb.trans_eq ?_
  unfold bernsteinEnergy
  field_simp
  <;> ring

end Erdos66BernsteinBudgetParameters
