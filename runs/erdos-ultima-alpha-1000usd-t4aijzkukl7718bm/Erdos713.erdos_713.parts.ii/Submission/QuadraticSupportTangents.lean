import FormalConjecturesUtil
import Submission.QuadraticSupports

/-! Secant control of quadratic supports. Only the explicit power function
is differentiated; no derivative of an asymptotic sequence is asserted. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713QuadraticSupportTangents
open Erdos713ExactCloneSaturation Erdos713QuadraticSupports
set_option maxHeartbeats 2000000

lemma scaled_ratio_limit {f : ℕ → ℕ} {α c t : ℝ} (ht : 0 < t)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => (f ⌊t*n⌋₊ : ℝ)/(n : ℝ)^α) atTop (𝓝 (c*t^α)) := by
  have hm : Tendsto (fun n : ℕ => ⌊t*(n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ht)
  have hr : Tendsto (fun n : ℕ => (⌊t*n⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht.le).comp tendsto_natCast_atTop_atTop
  have hp := hr.rpow_const (p := α) (Or.inl ht.ne')
  apply (((Erdos713FutureRecords.ratio_limit h).comp hm).mul hp).congr'
  filter_upwards [hm.eventually_gt_atTop 0,eventually_gt_atTop (0 : ℕ)] with n hm' hn
  have hmR : (0 : ℝ) < ⌊t*n⌋₊ := by exact_mod_cast hm'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply,Real.div_rpow hmR.le hnR.le]
  field_simp [(Real.rpow_pos_of_pos hmR α).ne']

lemma power_secant_limit (α c : ℝ) :
    Tendsto (fun t : ℝ => 2*c*(t^α-1)/(t^2-1)) (𝓝[≠] 1) (𝓝 (c*α)) := by
  have hd := (Real.hasDerivAt_rpow_const (x := 1) (p := α) (Or.inl one_ne_zero)).tendsto_slope
  change Tendsto (fun t => slope (fun x : ℝ => x^α) 1 t) _ _ at hd
  have hs : Tendsto (fun t : ℝ => (t^α-1)/(t-1)) (𝓝[≠] 1) (𝓝 α) := by
    simpa only [slope_def_field,Real.one_rpow,mul_one] using hd
  have hh := ((hs.const_mul (2*c)).div
    ((tendsto_id.mono_left nhdsWithin_le_nhds).add_const 1) (by norm_num : (1 : ℝ)+1 ≠ 0))
  convert hh using 1
  · funext t
    change 2*c*(t^α-1)/(t^2-1) = (2*c*((t^α-1)/(t-1)))/(t+1)
    rw [← mul_div_assoc,div_div]
    congr 1
    ring
  · congr 1
    ring

lemma exists_right_secant {α c a : ℝ} (ha : a < c*α) :
    ∃ t : ℝ, 1 < t ∧ a < 2*c*(t^α-1)/(t^2-1) := by
  have hh := ((power_secant_limit α c).mono_left (nhdsGT_le_nhdsNE 1)).eventually_const_lt ha
  obtain ⟨t,ht,hv⟩ := (eventually_mem_nhdsWithin.and hh).exists
  exact ⟨t,ht,hv⟩

lemma exists_left_secant {α c b : ℝ} (hb : c*α < b) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 2*c*(t^α-1)/(t^2-1) < b := by
  have hh := ((power_secant_limit α c).mono_left (nhdsLT_le_nhdsNE 1)).eventually_lt_const hb
  have hp : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,ht,hp,hv⟩ := (eventually_mem_nhdsWithin.and (hp.and hh)).exists
  exact ⟨t,hp,ht,hv⟩

lemma sequence_secant_limit {f : ℕ → ℕ} {α c t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ =>
      (((f ⌊t*n⌋₊ : ℝ)/(n : ℝ)^α - (f n : ℝ)/(n : ℝ)^α) /
        (((⌊t*n⌋₊ : ℝ)/(n : ℝ))^2-1)) * (2-(n : ℝ)⁻¹))
      atTop (𝓝 (2*c*(t^α-1)/(t^2-1))) := by
  have hr : Tendsto (fun n : ℕ => (⌊t*n⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht.le).comp tendsto_natCast_atTop_atTop
  have hne : t^2-1 ≠ 0 := by
    intro he
    have hs : t^2 = (1 : ℝ)^2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
    · exact ht1 he
    · linarith
  have hh := (((scaled_ratio_limit ht h).sub (Erdos713FutureRecords.ratio_limit h)).div
    ((hr.pow 2).sub_const 1) hne).mul
    (tendsto_natCast_atTop_atTop.inv_tendsto_atTop.const_sub 2)
  convert hh using 1
  congr 1
  ring

lemma normalized_secant_eq (f : ℕ → ℕ) (α : ℝ) {n m : ℕ} (hn : 0 < n) :
    (((f m : ℝ)/(n : ℝ)^α-(f n : ℝ)/(n : ℝ)^α)/
      (((m : ℝ)/(n : ℝ))^2-1))*(2-(n : ℝ)⁻¹) =
    ((f m : ℝ)-(f n : ℝ))/((m : ℝ)^2-(n : ℝ)^2) *
      ((2*(n : ℝ)-1)/(n : ℝ)^(α-1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_sub hnR,Real.rpow_one]
  have he : ((m : ℝ)/(n : ℝ))^2-1 = ((m : ℝ)^2-(n : ℝ)^2)/(n : ℝ)^2 := by
    field_simp
  rw [he]
  field_simp [hnR.ne', (Real.rpow_pos_of_pos hnR α).ne']

/-- Uniform lower tangent control at every sufficiently large support.
The curvature is allowed to depend on the support order. -/
theorem eventually_support_lower {f : ℕ → ℕ} {α c a : ℝ}
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (ha : a < c*α) :
    ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, QuadSupport f ε n →
      a*(n : ℝ)^(α-1) < ε*(2*(n : ℝ)-1) := by
  obtain ⟨t,ht,hat⟩ := exists_right_secant ha
  have ht0 : 0 < t := by linarith
  have hlim := sequence_secant_limit ht0 (ne_of_gt ht) h
  have hratio : Tendsto (fun n : ℕ => (⌊t*n⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht0.le).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_const_lt hat,hratio.eventually_const_lt ht,
    eventually_gt_atTop (0 : ℕ)] with n hs hm hn
  intro ε hrec
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (n : ℝ) < ⌊t*n⌋₊ := by
    have hh := (lt_div_iff₀ hnR).mp hm
    simpa only [one_mul] using hh
  have hd : 0 < (⌊t*n⌋₊ : ℝ)^2-(n : ℝ)^2 := by nlinarith
  have hr := hrec ⌊t*n⌋₊
  have hc : ((f ⌊t*n⌋₊ : ℝ)-(f n : ℝ))/
      ((⌊t*n⌋₊ : ℝ)^2-(n : ℝ)^2) ≤ ε := (div_le_iff₀ hd).mpr (by linarith)
  have hp := Real.rpow_pos_of_pos hnR (α-1)
  have hfac : 0 ≤ (2*(n : ℝ)-1)/(n : ℝ)^(α-1) :=
    div_nonneg (by linarith) hp.le
  have hh := mul_le_mul_of_nonneg_right hc hfac
  rw [normalized_secant_eq f α hn] at hs
  have hh' : a < ε*(2*(n : ℝ)-1)/(n : ℝ)^(α-1) := by
    simpa only [mul_div_assoc] using hs.trans_le hh
  exact (lt_div_iff₀ hp).mp hh'

/-- Uniform upper tangent control, obtained from orders below the support. -/
theorem eventually_support_upper {f : ℕ → ℕ} {α c b : ℝ}
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hb : c*α < b) :
    ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, QuadSupport f ε n →
      ε*(2*(n : ℝ)-1) < b*(n : ℝ)^(α-1) := by
  obtain ⟨t,ht0,ht,hbt⟩ := exists_left_secant hb
  have hlim := sequence_secant_limit ht0 (ne_of_lt ht) h
  have hratio : Tendsto (fun n : ℕ => (⌊t*n⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht0.le).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_lt_const hbt,hratio.eventually_lt_const ht,
    eventually_gt_atTop (0 : ℕ)] with n hs hm hn
  intro ε hrec
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ ⌊t*n⌋₊ := Nat.cast_nonneg _
  have hmR : (⌊t*n⌋₊ : ℝ) < n := by
    have hh := (div_lt_iff₀ hnR).mp hm
    simpa only [one_mul] using hh
  have hd : (⌊t*n⌋₊ : ℝ)^2-(n : ℝ)^2 < 0 := by nlinarith
  have hr := hrec ⌊t*n⌋₊
  have hc : ε ≤ ((f ⌊t*n⌋₊ : ℝ)-(f n : ℝ))/
      ((⌊t*n⌋₊ : ℝ)^2-(n : ℝ)^2) := (le_div_iff_of_neg hd).mpr (by linarith)
  have hp := Real.rpow_pos_of_pos hnR (α-1)
  have hfac : 0 ≤ (2*(n : ℝ)-1)/(n : ℝ)^(α-1) :=
    div_nonneg (by linarith) hp.le
  have hh := mul_le_mul_of_nonneg_right hc hfac
  rw [normalized_secant_eq f α hn] at hs
  have hh' : ε*(2*(n : ℝ)-1)/(n : ℝ)^(α-1) < b := by
    simpa only [mul_div_assoc] using hh.trans_lt hs
  exact (div_lt_iff₀ hp).mp hh'

/-- A support sequence has the expected normalized slope. This is not a
statement about consecutive differences of f. -/
theorem support_slope_limit {f : ℕ → ℕ} {α c : ℝ}
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    {n : ℕ → ℕ} {ε : ℕ → ℝ} (hn : Tendsto n atTop atTop)
    (hs : ∀ i, QuadSupport f (ε i) (n i)) :
    Tendsto (fun i => ε i*(2*(n i : ℝ)-1)/(n i : ℝ)^(α-1))
      atTop (𝓝 (c*α)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hn.eventually (eventually_support_lower h ha),
      hn.eventually (eventually_gt_atTop (0 : ℕ))] with i hi hni
    exact (lt_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hni) _)).mpr (hi _ (hs i))
  · intro b hb
    filter_upwards [hn.eventually (eventually_support_upper h hb),
      hn.eventually (eventually_gt_atTop (0 : ℕ))] with i hi hni
    exact (div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hni) _)).mpr (hi _ (hs i))

#print axioms scaled_ratio_limit
#print axioms power_secant_limit
#print axioms sequence_secant_limit
#print axioms eventually_support_lower
#print axioms eventually_support_upper
#print axioms support_slope_limit
end Erdos713QuadraticSupportTangents
