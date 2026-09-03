import FormalConjecturesUtil
import Submission.RescalingDiagnostic

/-! A fixed-size uniform vertex sample loses a nonzero fraction of the
extremal scale whenever the exponent is below two. The finite multiplier
is written explicitly; no graph-limit consistency is inferred. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713SamplingExtremalityLoss
open Erdos713RescalingDiagnostic
set_option maxHeartbeats 1000000

/-- The edge-retention multiplier for an m-vertex sample from n vertices,
where m=floor(t*n), expressed using real subtraction. -/
noncomputable def multiplier (t : ℝ) (n : ℕ) : ℝ :=
  (⌊t*(n : ℝ)⌋₊ : ℝ) * ((⌊t*(n : ℝ)⌋₊ : ℝ)-1) /
    ((n : ℝ)*((n : ℝ)-1))

/-- Expected retained edges, divided by the extremal scale at the sampled
order. This is an algebraic expression, not a probability-space definition. -/
noncomputable def retainedFraction (f : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  multiplier t n * (f n / f ⌊t*(n : ℝ)⌋₊)

lemma multiplier_limit {t : ℝ} (ht : 0 < t) :
    Tendsto (multiplier t) atTop (𝓝 (t^2)) := by
  have hr : Tendsto (fun n : ℕ => (⌊t*(n : ℝ)⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht.le).comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hh := (hr.mul (hr.sub hi)).div (tendsto_const_nhds.sub hi)
    (by norm_num : (1 : ℝ)-0 ≠ 0)
  simp only [sub_zero,div_one,← pow_two] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  dsimp [multiplier]
  field_simp [ne_of_gt (show (0 : ℝ) < n by linarith),ne_of_gt (sub_pos.mpr hnR)]

/-- Pure-power exactness determines the sampling loss, rather than removing it. -/
theorem retainedFraction_limit {f : ℕ → ℝ} {α c t : ℝ}
    (hc : c ≠ 0) (ht : 0 < t)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (retainedFraction f t) atTop (𝓝 (t^(2-α))) := by
  have hs := (rescaling_limit hc ht hf).inv₀ (Real.rpow_pos_of_pos ht α).ne'
  simp only [inv_div] at hs
  have hh := (multiplier_limit ht).mul hs
  have he : t^2 * (t^α)⁻¹ = t^(2-α) := by
    rw [Real.rpow_sub ht,Real.rpow_two,div_eq_mul_inv]
  rw [he] at hh
  exact hh

/-- A fixed sample fraction strictly between zero and one leaves a fixed
positive deficit when alpha<2. This holds for rational exponents too. -/
theorem eventual_fixed_loss {f : ℕ → ℝ} {α c t : ℝ}
    (hc : c ≠ 0) (ht : 0 < t) (ht1 : t < 1) (hα : α < 2)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop, retainedFraction f t n < 1-η := by
  have hp : t^(2-α) < 1 := Real.rpow_lt_one ht.le ht1 (sub_pos.mpr hα)
  refine ⟨(1-t^(2-α))/2,by linarith,?_⟩
  exact (retainedFraction_limit hc ht hf).eventually_lt_const (by linarith)

/-- Thus asymptotically optimal uniform sampling cannot be an extra lemma
derived from the conjecture's hypotheses with alpha<2. -/
theorem not_sampling_sharp {f : ℕ → ℝ} {α c t : ℝ}
    (hc : c ≠ 0) (ht : 0 < t) (ht1 : t < 1) (hα : α < 2)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    ¬ Tendsto (retainedFraction f t) atTop (𝓝 1) := by
  intro h
  have he := tendsto_nhds_unique (retainedFraction_limit hc ht hf) h
  have hp : t^(2-α) < 1 := Real.rpow_lt_one ht.le ht1 (sub_pos.mpr hα)
  exact (ne_of_lt hp) he

/-- The numerical consequence applies directly to the extremal-number
sequence; it does not require a particular extremal host selection. -/
theorem extremal_sampling_loss {q : ℕ} {G : SimpleGraph (Fin q)} {α c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) (ht1 : t < 1) (hα : α < 2)
    (hf : (fun n : ℕ => (SimpleGraph.extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      retainedFraction (fun n => (SimpleGraph.extremalNumber n G : ℝ)) t n < 1-η :=
  eventual_fixed_loss hc.ne' ht ht1 hα hf

#print axioms multiplier_limit
#print axioms retainedFraction_limit
#print axioms eventual_fixed_loss
#print axioms not_sampling_sharp
#print axioms extremal_sampling_loss
end Erdos713SamplingExtremalityLoss
