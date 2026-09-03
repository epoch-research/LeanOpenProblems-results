import FormalConjecturesUtil

/-! Summation of a power asymptotic. Only the explicit real power function
is differentiated, never an arbitrary asymptotic sequence. -/
open Filter Asymptotics Finset
open scoped Topology
namespace Erdos713PowerSum

lemma power_increment_limit (p : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((1 + (n : ℝ)⁻¹)^p - 1)) atTop (𝓝 p) := by
  have hd := (Real.hasDerivAt_rpow_const (x := 1) (p := p) (Or.inl one_ne_zero)).tendsto_slope_zero_right
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def,Real.one_rpow,smul_eq_mul,inv_inv,mul_one] using hd.comp hi

lemma power_increment_equiv {p : ℝ} (hp : 0 < p) :
    (fun n : ℕ => ((n+1 : ℕ) : ℝ)^p - (n : ℝ)^p) ~[atTop]
      (fun n : ℕ => p*(n : ℝ)^(p-1)) := by
  apply isEquivalent_of_tendsto_one
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    intro he
    exact (mul_ne_zero hp.ne' (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast hn) _).ne' he).elim
  have ht := (power_increment_limit p).div_const p
  rw [div_self hp.ne'] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : ((n : ℝ)+1)^p = (n : ℝ)^p * (1+(n : ℝ)⁻¹)^p := by
    rw [← Real.mul_rpow hnp.le (by positivity)]
    congr 1
    field_simp
  change (n : ℝ)*((1+(n : ℝ)⁻¹)^p-1)/p =
    (((n+1 : ℕ) : ℝ)^p-(n : ℝ)^p)/(p*(n : ℝ)^(p-1))
  rw [Nat.cast_add,Nat.cast_one,hf,Real.rpow_sub hnp,Real.rpow_one]
  field_simp [(Real.rpow_pos_of_pos hnp p).ne']

lemma sum_equiv {f g : ℕ → ℝ} (h : f ~[atTop] g) (hg : ∀ n, 0 ≤ g n)
    (hTop : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop) :
    (fun n => ∑ i ∈ range n, f i) ~[atTop] (fun n => ∑ i ∈ range n, g i) := by
  have hh := h.sum_range hg hTop
  change ((fun n => ∑ i ∈ range n, f i) - (fun n => ∑ i ∈ range n, g i)) =o[atTop]
    (fun n => ∑ i ∈ range n, g i)
  simpa only [Pi.sub_apply,sum_sub_distrib] using hh

lemma sum_power_equiv {p : ℝ} (hp : 0 < p) :
    (fun n : ℕ => ∑ i ∈ range n, (i : ℝ)^(p-1)) ~[atTop]
      (fun n : ℕ => (n : ℝ)^p / p) := by
  let d : ℕ → ℝ := fun n => (((n+1 : ℕ) : ℝ)^p - (n : ℝ)^p) / p
  have hd : ∀ n, 0 ≤ d n := by
    intro n
    apply div_nonneg _ hp.le
    exact sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg n) (by norm_num) hp.le)
  have hsum (n : ℕ) : ∑ i ∈ range n, d i = (n : ℝ)^p / p := by
    simp only [d,← sum_div]
    rw [sum_range_sub (fun i : ℕ => (i : ℝ)^p) n,Nat.cast_zero,Real.zero_rpow hp.ne',sub_zero]
  have hTop : Tendsto (fun n => ∑ i ∈ range n, d i) atTop atTop := by
    simp_rw [hsum]
    exact ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).atTop_div_const hp
  have he : (fun n : ℕ => (n : ℝ)^(p-1)) ~[atTop] d := by
    have hh := (power_increment_equiv hp).div (IsEquivalent.refl (u := fun _ : ℕ => p) (l := atTop))
    change d ~[atTop] (fun n : ℕ => p*(n : ℝ)^(p-1)/p) at hh
    simpa only [mul_div_cancel_left₀ _ hp.ne'] using hh.symm
  simpa only [hsum] using sum_equiv he hd hTop

lemma sum_asymptotic {f : ℕ → ℝ} {α c : ℝ} (hα : 0 ≤ α) (hc : 0 < c)
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    (fun n => ∑ i ∈ range n, f i) ~[atTop]
      (fun n : ℕ => c/(α+1)*(n : ℝ)^(α+1)) := by
  have hp : 0 < α+1 := by linarith
  have hPower : (fun n : ℕ => ∑ i ∈ range n, c*(i : ℝ)^α) ~[atTop]
      (fun n : ℕ => c/(α+1)*(n : ℝ)^(α+1)) := by
    have hh := (IsEquivalent.refl (u := fun _ : ℕ => c) (l := atTop)).mul (sum_power_equiv hp)
    change (fun n : ℕ => c * ∑ i ∈ range n, (i : ℝ)^(α+1-1)) ~[atTop]
      (fun n : ℕ => c*((n : ℝ)^(α+1)/(α+1))) at hh
    simpa only [add_sub_cancel_right,mul_sum,mul_div_assoc,div_mul_eq_mul_div] using hh
  have hTop : Tendsto (fun n : ℕ => ∑ i ∈ range n, c*(i : ℝ)^α) atTop atTop :=
    hPower.symm.tendsto_atTop (((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (div_pos hc hp))
  exact (sum_equiv h (fun n => by positivity) hTop).trans hPower

#print axioms power_increment_equiv
#print axioms sum_power_equiv
#print axioms sum_asymptotic
end Erdos713PowerSum
