import Submission.AbelErrorEnergyExplore

/-! Higher even Abel moments obtained from the checked second-moment
obstruction by Jensen's inequality. The coefficient is c^k, with no
factorial gain; this does not settle the logarithmic-limit conjecture. -/
namespace Erdos66AbelHigherMoment
open Filter AdditiveCombinatorics Erdos66Generating Erdos66AbelErrorEnergy
open scoped Topology Classical
set_option maxHeartbeats 1400000

lemma weighted_tsum_pow_le {w f : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hf : ∀ n, 0 ≤ f n) (hws : HasSum w 1)
    (hfs : Summable (fun n ↦ w n*f n)) (k : ℕ) (hk : k≠0)
    (hks : Summable (fun n ↦ w n*(f n)^k)) :
    (∑' n, w n*f n)^k ≤ ∑' n, w n*(f n)^k := by
  have hfinite (N : ℕ) :
      (∑ n∈Finset.range N, w n*f n)^k ≤ ∑ n∈Finset.range N, w n*(f n)^k := by
    have hwN : (∑ n∈Finset.range N, w n) ≤ 1 := by
      simpa only [hws.tsum_eq] using
        hws.summable.sum_le_tsum (Finset.range N) (fun n _ ↦ hw n)
    have hJ := (convexOn_pow k).map_add_sum_le
      (t := Finset.range N) (w := w) (p := f)
      (v := 1-∑ n∈Finset.range N, w n) (q := (0:ℝ))
      (fun n _ ↦ hw n) (by ring) (fun n _ ↦ hf n)
      (sub_nonneg.mpr hwN) (show (0:ℝ) ∈ Set.Ici 0 from le_refl (0:ℝ))
    simpa only [smul_eq_mul,mul_zero,zero_add,zero_pow hk] using hJ
  exact le_of_tendsto_of_tendsto (hfs.hasSum.tendsto_sum_nat.pow k)
    hks.hasSum.tendsto_sum_nat (Eventually.of_forall hfinite)

lemma geometric_weight_hasSum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r<1) :
    HasSum (fun n : ℕ ↦ (1-r)*r^n) 1 := by
  convert (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1-r) using 1
  exact (mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hr1))).symm

lemma geometric_power_mean {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r<1)
    (hfs : Summable (fun n ↦ f n*r^n)) (k : ℕ) (hk : k≠0)
    (hks : Summable (fun n ↦ (f n)^k*r^n)) :
    ((1-r)*series f r)^k ≤ (1-r)*series (fun n ↦ (f n)^k) r := by
  have h₁ : Summable (fun n ↦ ((1-r)*r^n)*f n) :=
    (hfs.mul_left (1-r)).congr (fun n ↦ by ring)
  have h₂ : Summable (fun n ↦ ((1-r)*r^n)*(f n)^k) :=
    (hks.mul_left (1-r)).congr (fun n ↦ by ring)
  have hh := weighted_tsum_pow_le (fun n ↦ mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr0 n))
    hf (geometric_weight_hasSum hr0 hr1) h₁ k hk h₂
  have he₁ : (∑' n, ((1-r)*r^n)*f n)=(1-r)*series f r := by
    rw [show (fun n ↦ ((1-r)*r^n)*f n)=(fun n ↦ (1-r)*(f n*r^n)) by funext n; ring,
      tsum_mul_left]
    rfl
  have he₂ : (∑' n, ((1-r)*r^n)*(f n)^k)=(1-r)*series (fun n ↦ (f n)^k) r := by
    rw [show (fun n ↦ ((1-r)*r^n)*(f n)^k)=(fun n ↦ (1-r)*((f n)^k*r^n)) by funext n; ring,
      tsum_mul_left]
    rfl
  simpa only [he₁,he₂] using hh

lemma summable_shifted_power_geometric (k : ℕ) {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    Summable (fun n : ℕ ↦ ((n:ℝ)+1)^k*r^n) := by
  have hh := (summable_nat_add_iff 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one k
      (show ‖r‖<1 by simpa only [Real.norm_eq_abs,abs_of_pos hr0] using hr1))
  apply (hh.mul_left r⁻¹).congr
  intro n
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp

lemma log_error_abs_bound (A : Set ℕ) (c : ℝ) (n : ℕ) :
    |(sumRep A n:ℝ)-c*Real.log n| ≤ (1+|c|)*((n:ℝ)+1) := by
  have hs : (sumRep A n:ℝ) ≤ (n:ℝ)+1 := by
    exact_mod_cast Erdos66Counting.sumRep_le_succ A n
  have hl0 : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hl1 : Real.log (n:ℝ) ≤ (n:ℝ)+1 := by
    rcases n with _ | n
    · simp
    · have hh := Real.log_le_sub_one_of_pos (show 0<((n+1:ℕ):ℝ) by positivity)
      linarith
  calc
    _ ≤ |(sumRep A n:ℝ)|+|c*Real.log n| := abs_sub _ _
    _ = (sumRep A n:ℝ)+|c| *Real.log n := by
      rw [abs_of_nonneg (Nat.cast_nonneg _),abs_mul,abs_of_nonneg hl0]
    _ ≤ (n:ℝ)+1+|c| *((n:ℝ)+1) :=
      add_le_add hs (mul_le_mul_of_nonneg_left hl1 (abs_nonneg _))
    _ = _ := by ring

lemma summable_log_error_even (A : Set ℕ) (c : ℝ) (k : ℕ)
    {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    Summable (fun n : ℕ ↦ ((sumRep A n:ℝ)-c*Real.log n)^(2*k)*r^n) := by
  apply ((summable_shifted_power_geometric (2*k) hr0 hr1).mul_left ((1+|c|)^(2*k))).of_norm_bounded
  intro n
  rw [norm_mul,Real.norm_eq_abs,abs_pow,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr0.le n)]
  calc
    _ ≤ ((1+|c|)*((n:ℝ)+1))^(2*k)*r^n :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (log_error_abs_bound A c n) _) (pow_nonneg hr0.le n)
    _ = _ := by rw [mul_pow]; ring

/-- Jensen transfer with the geometric probability weights. The normalization
is by the k-th power of the logarithm, not the k-th power of the kernel. -/
lemma normalized_even_moment_ge (A : Set ℕ) (c : ℝ) (k : ℕ) (hk : k≠0)
    {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    (series (fun n ↦ ((sumRep A n:ℝ)-c*Real.log n)^2) r*kernel r)^k ≤
      series (fun n ↦ ((sumRep A n:ℝ)-c*Real.log n)^(2*k)) r *
        (1-r)/(-Real.log (1-r))^k := by
  have hL : 0 < -Real.log (1-r) := by
    have hh := Real.log_neg (show 0<1-r by linarith) (show 1-r<1 by linarith)
    linarith
  have hs₁ := summable_log_error_even A c 1 hr0 hr1
  simp only [mul_one] at hs₁
  have hs₂ := summable_log_error_even A c k hr0 hr1
  have hh := geometric_power_mean (fun n ↦ sq_nonneg ((sumRep A n:ℝ)-c*Real.log n))
    hr0.le hr1 hs₁ k hk (by simpa only [←pow_mul] using hs₂)
  simp only [←pow_mul] at hh
  have hd := div_le_div_of_nonneg_right hh (pow_nonneg hL.le k)
  rw [kernel, ←mul_div_assoc, div_pow,
    mul_comm (series (fun n ↦ ((sumRep A n:ℝ)-c*Real.log n)^2) r) (1-r)]
  exact hd.trans_eq (by ring)

/-- A hypothetical witness has normalized 2k-th Abel error moment with lower
limit at least c^k. This is a consequence of the second moment, and does not
yield logarithmic-order pointwise fluctuations. -/
theorem normalized_even_moment_eventually_gt {A : Set ℕ} {c d : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (k : ℕ) (hk : k≠0) (hd : d<c^k) :
    ∀ᶠ r : ℝ in 𝓝[<] 1,
      d < series (fun n ↦ ((sumRep A n:ℝ)-c*Real.log n)^(2*k)) r *
        (1-r)/(-Real.log (1-r))^k := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hp : Tendsto (fun b : ℝ ↦ b^k) (𝓝[<] c) (𝓝 (c^k)) :=
    (continuous_pow k).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hbpos : ∀ᶠ b : ℝ in 𝓝[<] c, 0<b := nhdsWithin_le_nhds (Ioi_mem_nhds hcpos)
  obtain ⟨b,hbp,hb0,hbc⟩ := ((hp.eventually (lt_mem_nhds hd)).and
    (hbpos.and self_mem_nhdsWithin)).exists
  filter_upwards [logarithmic_error_energy_eventually_gt hc h hbc,unit_interval_eventually]
    with r hr hunit
  exact hbp.trans ((pow_lt_pow_left₀ hr hb0.le hk).trans_le
    (normalized_even_moment_ge A c k hk hunit.1 hunit.2))

end Erdos66AbelHigherMoment
