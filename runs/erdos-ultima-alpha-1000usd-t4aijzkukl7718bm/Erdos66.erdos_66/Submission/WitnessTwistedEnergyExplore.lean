import Submission.NaturalTwistedEnergyExplore
import Submission.WitnessAutocorrelationExplore
import Submission.RoundingExplore

/-! Mean-square parity imbalance is negligible for every hypothetical
logarithmic representation witness. No pointwise residue limit is asserted. -/
namespace Erdos66WitnessTwistedEnergy
open Erdos66TwistedEnergy Erdos66NaturalTwistedEnergy
  Erdos66WitnessAutocorrelation Erdos66AutocorrelationAbel
  Erdos66Generating Erdos66Fractional Erdos66FractionalFourthPower
  Erdos66SquareRootFluctuation Erdos66AbelErrorEnergy Erdos66Rounding
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2400000

lemma alternating_prefix_bound (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hm : Antitone f) (N : ℕ) : |∑ k∈Finset.range N, (-1)^k*f k| ≤ f 0 := by
  let g : ℕ → ℝ := fun k ↦ if k<N then f k else 0
  have hg0 (k : ℕ) : 0 ≤ g k := by dsimp [g]; split_ifs; exact hf k; rfl
  have hgm : Antitone g := by
    intro i j hij
    by_cases hj : j<N
    · have hi : i<N := by omega
      simp only [g,if_pos hj,if_pos hi]
      exact hm hij
    · simpa only [g,if_neg hj] using hg0 i
  have hgs : Summable g := summable_of_ne_finset_zero (s := Finset.range N)
    (fun k hk ↦ by simpa only [g,Finset.mem_range] using if_neg (by simpa using hk))
  have ht := alternating_series_error_bound g hgm hgs 0
  simp only [Finset.range_zero,Finset.sum_empty,sub_zero] at ht
  have he : (∑' k : ℕ, (-1)^k*g k)=∑ k∈Finset.range N, (-1)^k*f k := by
    rw [tsum_eq_sum (s := Finset.range N) (fun k hk ↦ by
      have hn : ¬k<N := by simpa only [Finset.mem_range] using hk
      simp only [g,if_neg hn,mul_zero])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [g,if_pos (Finset.mem_range.mp hk)]
  rw [he] at ht
  exact ht.trans (by dsimp [g]; split_ifs; rfl; exact hf 0)

lemma twist_profile_bound (n : ℕ) : |twistConv profile n| ≤ 2 := by
  have hb (k : ℕ) : |prefixSum (alt profile) k| ≤ (1 : ℝ) := by
    simpa only [prefixSum,alt,profile_zero] using
      alternating_prefix_bound profile profile_nonneg profile_antitone (k+1)
  simpa only [twistConv,sumConv_comm_real profile (alt profile),mul_one] using
    mixed_convolution_bound (alt profile) 1 (by norm_num) hb n

lemma twist_sqrt_scale {c : ℝ} (hc : 0 ≤ c) (f : ℕ → ℝ) (n : ℕ) :
    twistConv (fun k ↦ Real.sqrt c*f k) n=c*twistConv f n := by
  unfold twistConv sumConv alt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  calc
    _ = (Real.sqrt c)^2*(f ij.1*((-1)^ij.2*f ij.2)) := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

lemma summable_twist_profile_sq {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r<1) :
    Summable (fun n ↦ twistConv (fun k ↦ Real.sqrt c*profile k) n^2*r^n) := by
  apply ((summable_geometric_of_lt_one hr0 hr1).mul_left (4*c^2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hr0 _)),
    twist_sqrt_scale hc,mul_pow]
  have hs : twistConv profile n^2 ≤ 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (twist_profile_bound n) 2
    simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num] using hh
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg c))
    (pow_nonneg hr0 n)]

lemma twist_profile_series_bound {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r<1) :
    (∑' n, twistConv (fun k ↦ Real.sqrt c*profile k) n^2*r^n) ≤ 4*c^2/(1-r) := by
  have ht := (summable_twist_profile_sq hc hr0 hr1).tsum_le_tsum
    (fun n ↦ show twistConv (fun k ↦ Real.sqrt c*profile k) n^2*r^n ≤ (4*c^2)*r^n from by
      rw [twist_sqrt_scale hc,mul_pow]
      have hs := pow_le_pow_left₀ (abs_nonneg _) (twist_profile_bound n) 2
      rw [sq_abs] at hs
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg c))
        (pow_nonneg hr0 n)]) ((summable_geometric_of_lt_one hr0 hr1).mul_left (4*c^2))
  simpa only [tsum_mul_left,tsum_geometric_of_lt_one hr0 hr1,div_eq_mul_inv] using ht

noncomputable def twistEnergy (A : Set ℕ) (r : ℝ) : ℝ :=
  ∑' n, (twistConv (indicator A) n*r^n)^2

/-- A quantitative bound, valid for all A, without any limit assumption. -/
theorem witness_twisted_bound (A : Set ℕ) {c r : ℝ} (hc : 0 ≤ c)
    (hr0 : 0<r) (hr1 : r<1) :
    Summable (fun n ↦ (twistConv (indicator A) n*r^n)^2) ∧
    twistEnergy A r ≤ 4*c^2/(1-r)+
      Real.sqrt (series (errorSq A c) r*
        (4*series (errorSq A c) r+6*c^2*harmonicSqSeries r)) := by
  have hf := summable_indicator A (r := r) (by simpa only [abs_of_pos hr0] using hr1)
  have hg : Summable (fun n ↦ (Real.sqrt c*profile n)*r^n) := by
    simpa only [pow_one,mul_assoc] using
      (summable_profile_power_weighted hr0.le hr1 1).mul_left (Real.sqrt c)
  have hcA (n : ℕ) : sumConv (indicator A) (indicator A) n=(sumRep A n : ℝ) :=
    sum_indicator_antidiagonal A n
  have hf2 : Summable (fun n ↦ sumConv (indicator A) (indicator A) n^2*r^n) := by
    simpa only [hcA,errorSq,zero_mul,sub_zero] using summable_errorSq A 0 hr0.le hr1
  have hg2 : Summable (fun n ↦ sumConv (fun k ↦ Real.sqrt c*profile k)
      (fun k ↦ Real.sqrt c*profile k) n^2*r^n) := by
    simpa only [scaled_profile_convolution hc,mul_pow,mul_assoc] using
      (summable_harmonic_sq hr0.le hr1).mul_left (c^2)
  have hE : Summable (fun n ↦ (sumConv (indicator A) (indicator A) n-
      sumConv (fun k ↦ Real.sqrt c*profile k) (fun k ↦ Real.sqrt c*profile k) n)^2*r^n) := by
    simpa only [hcA,scaled_profile_convolution hc,errorSq] using summable_errorSq A c hr0.le hr1
  have hh := natural_twisted_energy_bound hr0.le hr1 hf hg hf2 hg2 hE
    (summable_twist_profile_sq hc hr0.le hr1)
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply add_le_add (twist_profile_series_bound hc hr0.le hr1)
  apply Real.sqrt_le_sqrt
  simp only [hcA,scaled_profile_convolution hc,mul_pow,mul_assoc,tsum_mul_left]
  change series (errorSq A c) r*(2*series (fun n ↦ (sumRep A n : ℝ)^2) r+
    2*(c^2*harmonicSqSeries r)) ≤ _
  apply mul_le_mul_of_nonneg_left _
    (tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr0.le n)))
  have hrep : series (fun n ↦ (sumRep A n : ℝ)^2) r ≤
      2*series (errorSq A c) r+2*c^2*harmonicSqSeries r := by
    have hp (n : ℕ) : (sumRep A n : ℝ)^2*r^n ≤
        2*(errorSq A c n*r^n)+(2*c^2)*((harmonic (n+1) : ℝ)^2*r^n) := by
      have hsq : (sumRep A n : ℝ)^2 ≤ 2*errorSq A c n+2*c^2*(harmonic (n+1) : ℝ)^2 := by
        dsimp [errorSq]
        nlinarith [sq_nonneg ((sumRep A n : ℝ)-2*c*(harmonic (n+1) : ℝ))]
      nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg hr0.le n)]
    have hs := (summable_errorSq A 0 hr0.le hr1)
    simp only [errorSq,zero_mul,sub_zero] at hs
    have ht := hs.tsum_le_tsum hp (((summable_errorSq A c hr0.le hr1).mul_left 2).add
      ((summable_harmonic_sq hr0.le hr1).mul_left (2*c^2)))
    simpa only [Summable.tsum_add ((summable_errorSq A c hr0.le hr1).mul_left 2)
      ((summable_harmonic_sq hr0.le hr1).mul_left (2*c^2)),tsum_mul_left,series,harmonicSqSeries]
      using ht
  linarith


lemma sqrt_multiply_kernel (a b k : ℝ) (hk : 0 ≤ k) :
    Real.sqrt (a*b)*k=Real.sqrt ((a*k)*(b*k)) := by
  calc
    _ = Real.sqrt (k^2)*Real.sqrt (a*b) := by rw [Real.sqrt_sq hk]; ring
    _ = Real.sqrt (k^2*(a*b)) := (Real.sqrt_mul (sq_nonneg k) _).symm
    _ = _ := congrArg Real.sqrt (by ring)

/-- The total squared alternating convolution is o(log²/(1-r)). This
allows exceptional targets and does not give pointwise residue splitting. -/
theorem witness_normalized_twist_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ twistEnergy A r*squareKernel r) (𝓝[<] 1) (𝓝 0) := by
  have hc := Erdos66Explore.limit_nonneg h
  let E : ℝ → ℝ := fun r ↦ series (errorSq A c) r*squareKernel r
  have hE : Tendsto E (𝓝[<] 1) (𝓝 0) := witness_normalized_error_energy_zero h
  have hlog : Tendsto (fun r : ℝ ↦ 4*c^2/(-Real.log (1-r))^2) (𝓝[<] 1) (𝓝 0) := by
    simpa only [div_pow,one_pow,mul_one_div,zero_pow (by decide : 2≠0),mul_zero] using
      ((negative_log_one_sub.const_div_atTop (1 : ℝ)).pow 2).const_mul (4*c^2)
  have hbound : Tendsto (fun r : ℝ ↦ 4*c^2/(-Real.log (1-r))^2+
      Real.sqrt (E r*(4*E r+36*c^2))) (𝓝[<] 1) (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add,Real.sqrt_zero,add_zero] using
      hlog.add ((hE.mul ((hE.const_mul 4).add_const (36*c^2))).sqrt)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [unit_interval_eventually] with r hr
    exact mul_nonneg (tsum_nonneg (fun _ ↦ sq_nonneg _)) (squareKernel_nonneg hr.2)
  · filter_upwards [unit_interval_eventually,
      negative_log_one_sub.eventually_ge_atTop 1] with r hr hL
    have hk := squareKernel_nonneg hr.2
    have he0 : 0 ≤ series (errorSq A c) r :=
      tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr.1.le n))
    have hEK : 0 ≤ E r := mul_nonneg he0 hk
    have hh := mul_le_mul_of_nonneg_right (witness_twisted_bound A hc hr.1 hr.2).2 hk
    rw [add_mul,sqrt_multiply_kernel _ _ _ hk] at hh
    have heq : 4*c^2/(1-r)*squareKernel r=4*c^2/(-Real.log (1-r))^2 := by
      dsimp [squareKernel]
      have ht : 1-r≠0 := (sub_pos.mpr hr.2).ne'
      field_simp
    rw [heq] at hh
    apply hh.trans
    apply add_le_add_right
    apply Real.sqrt_le_sqrt
    change E r*((4*series (errorSq A c) r+6*c^2*harmonicSqSeries r)*squareKernel r) ≤ _
    apply mul_le_mul_of_nonneg_left _ hEK
    have hH := harmonicSqSeries_normalized_bound hr.1 hr.2 hL
    have hmul := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 6*c^2)
    dsimp only [E]
    nlinarith

end Erdos66WitnessTwistedEnergy
