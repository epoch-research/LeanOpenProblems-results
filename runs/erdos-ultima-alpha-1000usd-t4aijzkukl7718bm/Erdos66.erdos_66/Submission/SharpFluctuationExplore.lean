import Submission.FrequentFluctuationExplore

/-! Geometric tilting removes the factor-two radial loss in the earlier
fluctuation bound. This remains a necessary condition, not a disproof. -/
namespace Erdos66SharpFluctuation
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating
  Erdos66FractionalFourthPower Erdos66SquareRootFluctuation Erdos66ResidueSeries
  Erdos66WeightedSquareStability Erdos66FrequentFluctuation
open scoped Topology Classical
set_option maxHeartbeats 800000

lemma weight_join (f : ℕ → ℝ) (r : ℝ) (k l n : ℕ) :
    (f n*(r^k)^n)*(r^l)^n = f n*(r^(k+l))^n := by
  rw [pow_add,mul_pow]
  ring

lemma square_weight_join (f : ℕ → ℝ) (r : ℝ) (k l n : ℕ) :
    (f n*(r^k)^n)^2*(r^l)^n = (f n)^2*(r^(2*k+l))^n := by
  rw [mul_pow,← pow_mul (r^k),Nat.mul_comm n 2,pow_mul (r^k)]
  rw [mul_assoc,← mul_pow,← pow_mul,← pow_add,Nat.mul_comm k 2]

lemma tilted_weighted_lower_bound {A : Set ℕ} {c r : ℝ} (k : ℕ)
    (hc : 0 ≤ c) (hr0 : 0 < r) (hr1 : r < 1)
    (hE : Summable (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2*
      (r^(2*k+1))^n)) :
    (max 0 (series (indicator A) (r^(2*k+2)) -
      c*series (fun n ↦ (profile n)^2) (r^(2*k+1))))^2 ≤
      series (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2) (r^(2*k+1)) := by
  let f : ℕ → ℝ := fun n ↦ indicator A n*(r^k)^n
  let g : ℕ → ℝ := fun n ↦ (Real.sqrt c*profile n)*(r^k)^n
  have hrpow (m : ℕ) (hm : m ≠ 0) : |r^m| < 1 := by
    rw [abs_of_nonneg (pow_nonneg hr0.le m)]
    exact pow_lt_one₀ hr0.le hr1 hm
  have hf : Summable (fun n ↦ f n*r^n) := by
    have he (n : ℕ) : f n*r^n = indicator A n*(r^(k+1))^n := by
      simpa only [pow_one] using weight_join (indicator A) r k 1 n
    simp_rw [he]
    exact summable_indicator A (hrpow _ (by omega))
  have hg : Summable (fun n ↦ g n*r^n) := by
    have he (n : ℕ) : g n*r^n = Real.sqrt c*(profile n*(r^(k+1))^n) := by
      dsimp [g]
      simpa only [pow_one,mul_assoc] using weight_join (fun n ↦ Real.sqrt c*profile n) r k 1 n
    simp_rw [he]
    exact (by simpa only [pow_one] using
      (summable_profile_power_weighted (pow_nonneg hr0.le (k+1))
        (pow_lt_one₀ hr0.le hr1 (by omega : k+1 ≠ 0)) 1).mul_left (Real.sqrt c))
  have hf2 : Summable (fun n ↦ (f n)^2*(r^2)^n) := by
    have he (n : ℕ) : (f n)^2*(r^2)^n = indicator A n*(r^(2*k+2))^n := by
      simpa only [indicator_square] using square_weight_join (indicator A) r k 2 n
    simp_rw [he]
    exact summable_indicator A (hrpow _ (by omega))
  have hg2 : Summable (fun n ↦ (g n)^2*r^n) := by
    have he (n : ℕ) : (g n)^2*r^n = c*((profile n)^2*(r^(2*k+1))^n) := by
      simpa only [g,pow_one,mul_pow,Real.sq_sqrt hc,mul_assoc] using
        square_weight_join (fun n ↦ Real.sqrt c*profile n) r k 1 n
    simp_rw [he]
    exact (summable_profile_power_weighted (pow_nonneg hr0.le _)
      (pow_lt_one₀ hr0.le hr1 (by omega : 2*k+1 ≠ 0)) 2).mul_left c
  have hconv (n : ℕ) : sumConv f f n-sumConv g g n =
      ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))*(r^k)^n := by
    dsimp only [f,g]
    have hcA : sumConv (indicator A) (indicator A) n = (sumRep A n : ℝ) :=
      sum_indicator_antidiagonal A n
    rw [weighted_convolution,weighted_convolution,scaled_profile_convolution hc,hcA,sub_mul]
  have heq (n : ℕ) : (sumConv f f n-sumConv g g n)^2*r^n =
      ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2*(r^(2*k+1))^n := by
    rw [hconv]
    simpa only [pow_one] using square_weight_join
      (fun n ↦ (sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ)) r k 1 n
  have hE' : Summable (fun n ↦ (sumConv f f n-sumConv g g n)^2*r^n) := by
    simpa only [heq] using hE
  have hh := weighted_square_stability_limit (f := f) (g := g) hr0.le hr1
    (fun n ↦ mul_nonneg (indicator_nonneg A n) (pow_nonneg (pow_nonneg hr0.le k) n))
    hf hg hf2 hg2 hE'
  have hfEq (n : ℕ) : (f n)^2*(r^2)^n = indicator A n*(r^(2*k+2))^n := by
    simpa only [indicator_square] using square_weight_join (indicator A) r k 2 n
  have hgEq (n : ℕ) : (g n)^2*r^n = c*((profile n)^2*(r^(2*k+1))^n) := by
    simpa only [g,pow_one,mul_pow,Real.sq_sqrt hc,mul_assoc] using
      square_weight_join (fun n ↦ Real.sqrt c*profile n) r k 1 n
  simpa only [hfEq,hgEq,heq,tsum_mul_left,series] using hh

lemma normalized_indicator_power_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun r : ℝ ↦ series (indicator A) (r^m)*Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 (Real.sqrt c/Real.sqrt m)) := by
  have hN : Tendsto (fun r : ℝ ↦ series (indicator A) r*Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 (Real.sqrt c)) := witness_generating_limit h
  have hh := (witness_generating_power_ratio hc h m hm).mul hN
  simp only [one_div,inv_mul_eq_div] at hh
  apply hh.congr'
  filter_upwards [hN.eventually_ne (Real.sqrt_ne_zero'.mpr (Erdos66Explore.limit_pos hc h))] with r hr
  have hF : series (indicator A) r ≠ 0 := (mul_ne_zero_iff.mp hr).1
  field_simp

lemma normalized_profile_square_power_limit (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun r : ℝ ↦ series (fun n ↦ (profile n)^2) (r^m)*Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 0) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hp := profile_square_series_limit.comp (power_tendsto_one_left m hm)
  have hh := hp.div (power_kernel_ratio m hm).sqrt (Real.sqrt_ne_zero'.mpr hmpos)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [unit_interval_eventually] with r hr
  have hk := kernel_pos hr.1 hr.2
  have hkm := kernel_pos (pow_pos hr.1 m) (pow_lt_one₀ hr.1.le hr.2 hm)
  change (series (fun n ↦ (profile n)^2) (r^m)*Real.sqrt (kernel (r^m))) /
    Real.sqrt (kernel (r^m)/kernel r) = _
  have hsk := Real.sqrt_ne_zero'.mpr hk
  have hskm := Real.sqrt_ne_zero'.mpr hkm
  rw [Real.sqrt_div hkm.le]
  field_simp

lemma normalized_series_power_limit {f : ℕ → ℝ} {d : ℝ}
    (hf : Tendsto (fun n ↦ f n/Real.log n) atTop (𝓝 d)) (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun r : ℝ ↦ series f (r^m)*kernel r) (𝓝[<] 1) (𝓝 (d/m)) := by
  have hbase : Tendsto (fun r : ℝ ↦ series f r*kernel r) (𝓝[<] 1) (𝓝 d) := by
    simpa only [kernel,mul_div_assoc] using logarithmic_abelian_limit hf
      (fun r hr0 hr1 ↦ summable_of_log_limit hf hr0 hr1)
  have hh := (hbase.comp (power_tendsto_one_left m hm)).div
    (power_kernel_ratio m hm) (by exact_mod_cast hm : (m : ℝ) ≠ 0)
  apply hh.congr'
  filter_upwards [unit_interval_eventually] with r hr
  have hk := kernel_pos hr.1 hr.2
  have hkm := kernel_pos (pow_pos hr.1 m) (pow_lt_one₀ hr.1.le hr.2 hm)
  change (series f (r^m)*kernel (r^m))/(kernel (r^m)/kernel r) = _
  field_simp

/-- The tilted radial comparison, before letting the tilt grow. -/
lemma tilted_envelope_limit_bound {A : Set ℕ} {c d : ℝ} {f : ℕ → ℝ}
    (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (hf : Tendsto (fun n ↦ f n/Real.log n) atTop (𝓝 d))
    (hdom : ∀ n : ℕ, ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2 ≤ f n)
    (k : ℕ) : c/((2*k+2 : ℕ) : ℝ) ≤ d/((2*k+1 : ℕ) : ℝ) := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hleft0 := (normalized_indicator_power_limit hc h (2*k+2) (by omega)).sub
    ((normalized_profile_square_power_limit (2*k+1) (by omega)).const_mul c)
  simp only [mul_zero,sub_zero] at hleft0
  have hleft := ((show Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[<] 1) (𝓝 0) from
    tendsto_const_nhds).max hleft0).pow 2
  have hmpos : (0 : ℝ) < (2*k+2 : ℕ) := by positivity
  have hspos : 0 < Real.sqrt c/Real.sqrt ((2*k+2 : ℕ) : ℝ) :=
    div_pos (Real.sqrt_pos.mpr hcpos) (Real.sqrt_pos.mpr hmpos)
  rw [max_eq_right hspos.le,div_pow,Real.sq_sqrt hcpos.le,Real.sq_sqrt hmpos.le] at hleft
  apply le_of_tendsto_of_tendsto hleft (normalized_series_power_limit hf (2*k+1) (by omega))
  filter_upwards [unit_interval_eventually] with r hr
  have hrm0 : 0 < r^(2*k+1) := pow_pos hr.1 _
  have hrm1 : r^(2*k+1) < 1 := pow_lt_one₀ hr.1.le hr.2 (by omega)
  have hfs := summable_of_log_limit hf hrm0 hrm1
  have hEs : Summable (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2*
      (r^(2*k+1))^n) := by
    apply hfs.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hdom n) (pow_nonneg hrm0.le n)
  have he_le : series (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2) (r^(2*k+1)) ≤
      series f (r^(2*k+1)) :=
    hEs.tsum_le_tsum (fun n ↦ mul_le_mul_of_nonneg_right (hdom n) (pow_nonneg hrm0.le n)) hfs
  have hbound := (tilted_weighted_lower_bound k hcpos.le hr.1 hr.2 hEs).trans he_le
  have hk := (kernel_pos hr.1 hr.2).le
  have hb := mul_le_mul_of_nonneg_right hbound hk
  have heq : (max 0 (series (indicator A) (r^(2*k+2))*Real.sqrt (kernel r) -
      c*(series (fun n ↦ (profile n)^2) (r^(2*k+1))*Real.sqrt (kernel r))))^2 =
      (max 0 (series (indicator A) (r^(2*k+2))-
        c*series (fun n ↦ (profile n)^2) (r^(2*k+1))))^2*kernel r := by
    calc
      _ = (max 0 (series (indicator A) (r^(2*k+2))-
          c*series (fun n ↦ (profile n)^2) (r^(2*k+1)))*Real.sqrt (kernel r))^2 := by
        rw [max_mul_of_nonneg _ _ (Real.sqrt_nonneg _),zero_mul,sub_mul]
        congr 2
        ring
      _ = _ := by rw [mul_pow,Real.sq_sqrt hk]
  rw [heq]
  exact hb

/-- Removing the radial loss improves c/2 to c. This is still only a
necessary condition for the original witness. -/
theorem sharp_error_envelope_limit_lower_bound {A : Set ℕ} {c d : ℝ} {f : ℕ → ℝ}
    (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (hf : Tendsto (fun n ↦ f n/Real.log n) atTop (𝓝 d))
    (hdom : ∀ᶠ n : ℕ in atTop,
      ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2 ≤ f n) : c ≤ d := by
  let g : ℕ → ℝ := fun n ↦ max (((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2) (f n)
  have hg : Tendsto (fun n ↦ g n/Real.log n) atTop (𝓝 d) := by
    apply hf.congr'
    filter_upwards [hdom] with n hn
    simp only [g,max_eq_right hn]
  have hk (k : ℕ) : c*((2*k+1 : ℕ) : ℝ) ≤ d*((2*k+2 : ℕ) : ℝ) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mp
      (tilted_envelope_limit_bound hc h hg (fun n ↦ le_max_left _ _) k)
  by_contra hcd
  have hdc : d < c := lt_of_not_ge hcd
  have hp : 0 < 2*(c-d) := by linarith
  obtain ⟨k,hkbig⟩ := exists_nat_gt ((2*d-c)/(2*(c-d)))
  have hh := (div_lt_iff₀ hp).mp hkbig
  have hh' := hk k
  push_cast at hh'
  nlinarith

lemma sharp_eventual_squared_error_bound {A : Set ℕ} {c d : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (he : ∀ᶠ n : ℕ in atTop,
      ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2/Real.log n ≤ d) : c ≤ d := by
  have hf : Tendsto (fun n : ℕ ↦ (d*Real.log n)/Real.log n) atTop (𝓝 d) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    exact (mul_div_cancel_right₀ d hl).symm
  apply sharp_error_envelope_limit_lower_bound hc h hf
  filter_upwards [he,eventually_ge_atTop 2] with n hn hn2
  exact (div_le_iff₀ (Real.log_pos (by exact_mod_cast hn2))).mp hn

theorem sharp_frequently_squared_error_gt {A : Set ℕ} {c d : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) (hd : d < c) :
    ∃ᶠ n : ℕ in atTop,
      d < ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2/Real.log n := by
  by_contra hh
  have he : ∀ᶠ n : ℕ in atTop,
      ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2/Real.log n ≤ d := by
    simpa only [not_lt] using not_frequently.mp hh
  exact (not_le.mpr hd) (sharp_eventual_squared_error_bound hc h he)

/-- In particular no witness has harmonic-centered fluctuations eventually
bounded by a*sqrt(log n) when a is nonnegative and a²<c. -/
theorem sharp_frequently_abs_harmonic_error_gt {A : Set ℕ} {c a : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (ha : 0 ≤ a) (ha2 : a^2 < c) :
    ∃ᶠ n : ℕ in atTop,
      a*Real.sqrt (Real.log n) < |(sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ)| := by
  apply ((sharp_frequently_squared_error_gt hc h ha2).and_eventually
    (eventually_ge_atTop 2)).mono
  intro n hn
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn.2)
  apply (sq_lt_sq₀ (mul_nonneg ha (Real.sqrt_nonneg _)) (abs_nonneg _)).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt hl.le]
  exact (lt_div_iff₀ hl).mp hn.1

/-- The same fluctuation lower bound holds with the conjecture's natural
center c*log n in place of the exact harmonic model. -/
theorem sharp_frequently_abs_log_error_gt {A : Set ℕ} {c a : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (ha : 0 ≤ a) (ha2 : a^2 < c) :
    ∃ᶠ n : ℕ in atTop,
      a*Real.sqrt (Real.log n) < |(sumRep A n : ℝ)-c*Real.log n| := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hhalf : 0 ≤ c := by positivity
  have hasqrt : a < Real.sqrt (c) := by
    apply (sq_lt_sq₀ ha (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt hhalf]
  obtain ⟨b,hab,hbsqrt⟩ := exists_between hasqrt
  have hb : 0 ≤ b := ha.trans hab.le
  have hb2 : b^2 < c := by
    simpa only [Real.sq_sqrt hhalf] using
      (sq_lt_sq₀ hb (Real.sqrt_nonneg (c))).mpr hbsqrt
  have hclose := (harmonic_log_center_difference_limit c).eventually
    (gt_mem_nhds (sub_pos.mpr hab))
  apply (((sharp_frequently_abs_harmonic_error_gt hc h hb hb2).and_eventually hclose).and_eventually
    (eventually_ge_atTop 2)).mono
  intro n hn
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn.2)
  have hs : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hl
  have hdist := (div_lt_iff₀ hs).mp hn.1.2
  have htri := abs_sub_le (sumRep A n : ℝ) (c*Real.log n) (c*(harmonic (n+1) : ℝ))
  have heq : |c*Real.log n-c*(harmonic (n+1) : ℝ)| =
      |c*((harmonic (n+1) : ℝ)-Real.log n)| := by
    rw [abs_sub_comm,← mul_sub]
  rw [heq] at htri
  nlinarith [hn.1.1]

/-- Explicit arbitrarily-large-target form of the log-centered result. -/
theorem sharp_exists_large_log_fluctuation {A : Set ℕ} {c a : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (ha : 0 ≤ a) (ha2 : a^2 < c) (N : ℕ) :
    ∃ n ≥ N, a*Real.sqrt (Real.log n) < |(sumRep A n : ℝ)-c*Real.log n| :=
  frequently_atTop.mp (sharp_frequently_abs_log_error_gt hc h ha ha2) N

end Erdos66SharpFluctuation
