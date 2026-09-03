import Submission.GeneratingExplore
import Submission.ConvRigidityExplore

/-! Residue-class pushforwards of summable sequences and generating functions.
These support necessary conditions for a logarithmic representation limit. -/
namespace Erdos66ResidueSeries
open Filter AdditiveCombinatorics Erdos66Generating Erdos66MixedEnergy
open scoped Topology Classical
variable (m : ℕ) [NeZero m]

noncomputable def residueTerm (f : ℕ → ℝ) (z : ZMod m) (n : ℕ) : ℝ :=
  if (n : ZMod m) = z then f n else 0

noncomputable def push (f : ℕ → ℝ) (z : ZMod m) : ℝ := ∑' n, residueTerm m f z n

lemma summable_residueTerm {f : ℕ → ℝ} (hf : Summable f) (z : ZMod m) :
    Summable (residueTerm m f z) := by
  convert hf.indicator {n : ℕ | (n : ZMod m) = z} using 1
  funext n
  simp only [residueTerm, Set.indicator_apply, Set.mem_setOf_eq]

lemma sum_push {f : ℕ → ℝ} (hf : Summable f) : (∑ z : ZMod m, push m f z) = ∑' n, f n := by
  simp only [push]
  rw [← Summable.tsum_finsetSum (fun z _ ↦ summable_residueTerm m hf z)]
  apply tsum_congr
  intro n
  simp [residueTerm, eq_comm]

lemma residue_nat_cast (k j : ℕ) : ((k * m + j : ℕ) : ZMod m) = j := by simp

lemma push_eq_subsequence {f : ℕ → ℝ} (z : ZMod m) :
    push m f z = ∑' k : ℕ, f (k * m + z.val) := by
  unfold push
  apply tsum_eq_tsum_of_ne_zero_bij (fun k ↦ k.val * m + z.val)
  · intro k l he
    apply Subtype.ext
    have hm := NeZero.pos m
    nlinarith
  · intro n hn
    have hres : (n : ZMod m) = z := by
      by_contra h
      exact hn (by simp [residueTerm, h])
    have hv : n % m = z.val := by
      have hh := congrArg ZMod.val hres
      simpa only [ZMod.val_natCast] using hh
    have he : n / m * m + z.val = n := by
      have hd := Nat.div_add_mod n m
      rw [Nat.mul_comm] at hd
      omega
    have hf : f (n / m * m + z.val) ≠ 0 := by
      rw [he]
      simpa only [Function.mem_support, residueTerm, if_pos hres] using hn
    exact ⟨⟨n / m, hf⟩, he⟩
  · intro k
    simp [residueTerm]

lemma residue_terms_conv (f g : ℕ → ℝ) (z : ZMod m) (n : ℕ) :
    (∑ a : ZMod m, ∑ ij ∈ Finset.antidiagonal n,
      residueTerm m f a ij.1 * residueTerm m g (z - a) ij.2) =
        residueTerm m (sumConv f g) z n := by
  rw [Finset.sum_comm]
  unfold residueTerm sumConv
  calc
    _ = ∑ ij ∈ Finset.antidiagonal n,
        if (n : ZMod m) = z then f ij.1 * g ij.2 else 0 := by
      apply Finset.sum_congr rfl
      intro ij hij
      have he : (ij.2 : ZMod m) = z - ij.1 ↔ (n : ZMod m) = z := by
        have hsum := Finset.mem_antidiagonal.mp hij
        rw [← hsum, Nat.cast_add]
        constructor <;> intro hh <;> linear_combination hh
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp only [he]
      split_ifs <;> simp
    _ = _ := by split_ifs <;> simp_all

lemma push_convolution {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (z : ZMod m) :
    conv (push m f) (push m g) z = push m (sumConv f g) z := by
  have hs (a : ZMod m) : Summable (fun n ↦ ∑ ij ∈ Finset.antidiagonal n,
      residueTerm m f a ij.1 * residueTerm m g (z - a) ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (summable_mul_of_summable_norm (summable_residueTerm m hf a).norm
        (summable_residueTerm m hg (z - a)).norm)
  unfold conv push
  simp_rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_residueTerm m hf _).norm (summable_residueTerm m hg _).norm]
  rw [← Summable.tsum_finsetSum (fun a _ ↦ hs a)]
  apply tsum_congr
  intro n
  exact residue_terms_conv m f g z n

lemma affine_tendsto (j : ℕ) : Tendsto (fun n : ℕ ↦ n * m + j) atTop atTop :=
  tendsto_atTop_mono (fun n ↦ by change n ≤ _; have hm := NeZero.pos m; nlinarith) tendsto_id

lemma log_affine_ratio (j : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.log (n * m + j : ℕ) / Real.log n) atTop (𝓝 1) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hj := tendsto_natCast_atTop_atTop.const_div_atTop (j : ℝ)
  have hsum := hj.const_add (m : ℝ)
  simp only [add_zero] at hsum
  have hlog := (Real.continuousAt_log hm).tendsto.comp hsum
  have hdiv := hlog.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hh := hdiv.const_add 1
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  have hfactor : (n * m + j : ℝ) = n * (m + j / n) := by field_simp
  have hright : (m : ℝ) + j / n ≠ 0 := by positivity
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_mul]
  rw [hfactor, Real.log_mul hn0 hright, add_div, div_self hnlog]

lemma affine_log_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ f (n * m + j) / Real.log n) atTop (𝓝 c) := by
  have hh := (h.comp (affine_tendsto m j)).mul (log_affine_ratio m j)
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hbig : 1 < n * m + j := by have hm := NeZero.pos m; nlinarith
  have hl : Real.log (n * m + j : ℕ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hbig))
  simp only [Function.comp_apply]
  field_simp

lemma summable_of_log_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : Summable (fun n ↦ f n * r ^ n) := by
  obtain ⟨D, hD, hb⟩ := global_harmonic_error h (by norm_num : (0 : ℝ) < 1)
  have hbound (n : ℕ) : |f n| ≤ (1 + |c|) * n + D := by
    calc
      |f n| = |(f n - c * (harmonic n : ℝ)) + c * (harmonic n : ℝ)| := by ring_nf
      _ ≤ |f n - c * (harmonic n : ℝ)| + |c * (harmonic n : ℝ)| := abs_add_le _ _
      _ ≤ (harmonic n : ℝ) + D + |c| * (harmonic n : ℝ) := by
        rw [abs_mul, abs_of_nonneg (harmonic_nonneg n)]
        linarith [hb n]
      _ ≤ (1 + |c|) * n + D := by
        have hh := mul_le_mul_of_nonneg_left (harmonic_le_nat n)
          (show 0 ≤ 1 + |c| by positivity)
        nlinarith
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hs₁ := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left (1 + |c|)
  have hs₂ := (summable_geometric_of_lt_one hr0.le hr1).mul_left D
  apply Summable.of_norm_bounded (hs₁.add hs₂)
  intro n
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hr0, pow_one]
  nlinarith [mul_le_mul_of_nonneg_right (hbound n) (pow_nonneg hr0.le n)]

lemma push_series_formula (f : ℕ → ℝ) (r : ℝ) (z : ZMod m) :
    push m (fun n ↦ f n * r ^ n) z =
      r ^ z.val * series (fun k ↦ f (k * m + z.val)) (r ^ m) := by
  rw [push_eq_subsequence, series, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [pow_add, show r ^ (k * m) = (r ^ m) ^ k by rw [← pow_mul, Nat.mul_comm]]
  ring

/-- Abelian equidistribution of the logarithmic representation sequence. -/
lemma push_series_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) (z : ZMod m) :
    Tendsto (fun r : ℝ ↦ push m (fun n ↦ f n * r ^ n) z * kernel r)
      (𝓝[<] 1) (𝓝 (c / m)) := by
  have hsub := affine_log_limit m h z.val
  have hlim : Tendsto (fun r : ℝ ↦ series (fun k ↦ f (k * m + z.val)) r * kernel r)
      (𝓝[<] 1) (𝓝 c) := by
    simpa only [kernel, mul_div_assoc] using logarithmic_abelian_limit hsub
      (fun r hr0 hr1 ↦ summable_of_log_limit hsub hr0 hr1)
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hp : Tendsto (fun r : ℝ ↦ r ^ z.val) (𝓝[<] 1) (𝓝 1) := by
    simpa only [one_pow] using ((continuous_pow z.val).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hh := (hp.mul (hlim.comp (power_tendsto_one_left m (NeZero.ne m)))).div
    (power_kernel_ratio m (NeZero.ne m)) hm
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [unit_interval_eventually] with r hr
  have hk := ne_of_gt (kernel_pos hr.1 hr.2)
  have hkm := ne_of_gt (kernel_pos (pow_pos hr.1 m) (pow_lt_one₀ hr.1.le hr.2 (NeZero.ne m)))
  simp only [Pi.div_apply, Function.comp_apply, push_series_formula]
  field_simp

end Erdos66ResidueSeries
