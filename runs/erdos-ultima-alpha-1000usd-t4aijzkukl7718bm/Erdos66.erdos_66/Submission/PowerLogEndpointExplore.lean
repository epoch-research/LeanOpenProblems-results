import Submission.WeightedEndpointObstructionExplore

/-!
Power–log weights cannot transfer the conjectural unweighted asymptotic
pointwise. These statements concern a different, weighted convolution.
They do not settle the conjecture in Spec.lean.
-/
namespace Erdos66PowerLogEndpoint
open Filter AdditiveCombinatorics Erdos66WeightedEndpoint
open scoped Topology

noncomputable def powerLogWeight (α β : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ (-α) * (Real.log ((n : ℝ) + 2)) ^ (-β)

noncomputable def powerLogScale (α β : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ (2 * α) * (Real.log ((n : ℝ) + 2)) ^ (2 * β - 1)

lemma shifted_log_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 2) :=
  Real.log_pos (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

lemma powerLogWeight_pos (α β : ℝ) (n : ℕ) : 0 < powerLogWeight α β n := by
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (shifted_log_pos n) _)

lemma powerLogWeight_antitone {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Antitone (powerLogWeight α β) := by
  intro n m hnm
  have hnm' : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hnm 2
  have hlog : Real.log ((n : ℝ) + 2) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by positivity) hnm'
  exact mul_le_mul
    (Real.rpow_le_rpow_of_nonpos (by positivity) hnm' (by linarith))
    (Real.rpow_le_rpow_of_nonpos (shifted_log_pos n) hlog (by linarith))
    (Real.rpow_nonneg (shifted_log_pos m).le _) (Real.rpow_nonneg (by positivity) _)

lemma powerLogScale_pos (α β : ℝ) (n : ℕ) : 0 < powerLogScale α β n := by
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (shifted_log_pos n) _)

lemma weight_mul_scale (α β : ℝ) (n : ℕ) :
    powerLogWeight α β n * powerLogScale α β n =
      ((n : ℝ) + 2) ^ α * (Real.log ((n : ℝ) + 2)) ^ (β - 1) := by
  unfold powerLogWeight powerLogScale
  calc
    _ = (((n : ℝ) + 2) ^ (-α) * ((n : ℝ) + 2) ^ (2 * α)) *
        ((Real.log ((n : ℝ) + 2)) ^ (-β) *
          (Real.log ((n : ℝ) + 2)) ^ (2 * β - 1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by positivity), ← Real.rpow_add (shifted_log_pos n)]
      congr 2 <;> ring

lemma weight_mul_scale_tendsto {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    Tendsto (fun n ↦ powerLogWeight α β n * powerLogScale α β n) atTop atTop := by
  have hx : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  apply tendsto_atTop_mono' atTop ?_ (power_over_log_tendsto α hα)
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  rw [weight_mul_scale]
  rw [div_eq_mul_inv, ← Real.rpow_neg_one]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
    (Real.rpow_nonneg (by positivity) _)

/-- This excludes the proposed pointwise weighted main term for every infinite
set, without assuming anything about its unweighted representation counts. -/
theorem powerLog_endpoint_peaks {A : Set ℕ} (hA : A.Infinite)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N,
      R < weightedRep A (powerLogWeight α β) n * powerLogScale α β n := by
  exact endpoint_peaks hA _ _ (powerLogWeight_pos α β)
    (powerLogWeight_antitone hα.le hβ) (fun n ↦ (powerLogScale_pos α β n).le)
    (weight_mul_scale_tendsto hα hβ)

theorem powerLog_no_finite_limit {A : Set ℕ} (hA : A.Infinite)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (c : ℝ) :
    ¬ Tendsto (fun n ↦ weightedRep A (powerLogWeight α β) n * powerLogScale α β n)
      atTop (𝓝 c) := by
  exact no_finite_weighted_limit hA _ _ (powerLogWeight_pos α β)
    (powerLogWeight_antitone hα.le hβ) (fun n ↦ (powerLogScale_pos α β n).le)
    (weight_mul_scale_tendsto hα hβ) c

/-- In particular, the log-log energy weight has unbounded normalized peaks.
Its normalization is sqrt(n+2) * sqrt(log(n+2)), not the original log(n). -/
theorem critical_weight_no_finite_limit {A : Set ℕ} (hA : A.Infinite) (c : ℝ) :
    ¬ Tendsto (fun n ↦ weightedRep A
      (fun k ↦ ((k : ℝ) + 2) ^ (-(1 / 4 : ℝ)) *
        (Real.log ((k : ℝ) + 2)) ^ (-(3 / 4 : ℝ))) n *
      (((n : ℝ) + 2) ^ (1 / 2 : ℝ) *
        (Real.log ((n : ℝ) + 2)) ^ (1 / 2 : ℝ))) atTop (𝓝 c) := by
  simpa only [powerLogWeight, powerLogScale, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num,
    show (2 : ℝ) * (3 / 4) - 1 = 1 / 2 by norm_num] using
    (powerLog_no_finite_limit hA (α := (1 / 4 : ℝ)) (β := (3 / 4 : ℝ))
      (by norm_num) (by norm_num) c)

end Erdos66PowerLogEndpoint
