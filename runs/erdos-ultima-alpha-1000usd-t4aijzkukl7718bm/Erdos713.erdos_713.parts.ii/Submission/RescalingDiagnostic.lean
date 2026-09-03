import FormalConjecturesUtil
import Submission.PolynomialRateCriterion
import Submission.DensitySequenceDiagnostic

/-! Fixed positive rescaling limits follow from every pure-power asymptotic,
including the irrational numerical diagnostics. They impose no additional
graph-specific maximality condition. This does not settle Erdős 713. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713RescalingDiagnostic

lemma scaled_power_ratio {f : ℕ → ℝ} {α c t : ℝ} (ht : 0 < t)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f ⌊t*n⌋₊/(n : ℝ)^α) atTop (𝓝 (c*t^α)) := by
  have hm : Tendsto (fun n : ℕ => ⌊t*(n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ht)
  have hr : Tendsto (fun n : ℕ => (⌊t*n⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht.le).comp tendsto_natCast_atTop_atTop
  have hp := hr.rpow_const (p := α) (Or.inl ht.ne')
  apply (((Erdos713PolynomialRate.ratio_limit hf).comp hm).mul hp).congr'
  filter_upwards [hm.eventually_gt_atTop 0,eventually_gt_atTop (0 : ℕ)] with n hm' hn
  have hmR : (0 : ℝ) < ⌊t*n⌋₊ := by exact_mod_cast hm'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply,Real.div_rpow hmR.le hnR.le]
  field_simp [(Real.rpow_pos_of_pos hmR α).ne']

/-- This holds for every positive real scale, not just integer scales. -/
theorem rescaling_limit {f : ℕ → ℝ} {α c t : ℝ} (hc : c ≠ 0) (ht : 0 < t)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f ⌊t*n⌋₊/f n) atTop (𝓝 (t^α)) := by
  have hh := (scaled_power_ratio ht hf).div (Erdos713PolynomialRate.ratio_limit hf) hc
  have hv : c*t^α/c = t^α := by field_simp
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_div_div_cancel_right₀ (Real.rpow_pos_of_pos hnR α).ne' _ _

/-- All the previously checked numerical extremal constraints, together
with every fixed positive rescaling limit, still allow an irrational index. -/
theorem exists_irrational_with_rescaling (N : ℕ) :
    ∃ (r c : ℝ) (f : ℕ → ℕ), (6 : ℝ)/5 < r ∧ r < (5 : ℝ)/4 ∧ Irrational r ∧
      0 < c ∧ Monotone f ∧ (∀ a b, f a+f b ≤ f (a+b)) ∧
      (∀ n, f n ≤ n.choose 2) ∧ (∀ n ≤ N, f n = n.choose 2) ∧
      AntitoneOn (fun n : ℕ => (f n : ℝ)/(n.choose 2 : ℝ)) (Set.Ici 2) ∧
      IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => c*(n : ℝ)^r) ∧
      ∀ t : ℝ, 0 < t →
        Tendsto (fun n : ℕ => (f ⌊t*n⌋₊ : ℝ)/(f n : ℝ)) atTop (𝓝 (t^r)) := by
  obtain ⟨r,c,f,hr,hr',hi,hc,hm,hs,hb,hp,hd,ha⟩ :=
    Erdos713DensitySequence.exists_irrational_sequence_with_prefix N
  exact ⟨r,c,f,hr,hr',hi,hc,hm,hs,hb,hp,hd,ha,
    fun _ ht => rescaling_limit hc.ne' ht ha⟩

#print axioms rescaling_limit
#print axioms exists_irrational_with_rescaling
end Erdos713RescalingDiagnostic
