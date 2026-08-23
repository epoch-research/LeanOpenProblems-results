import FormalConjectures.Util.ProblemImports

open Complex Filter Topology Set Finset
open scoped Real

noncomputable section

private lemma exp_two_pi_I_ne_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Complex.exp (2 * Real.pi * x * Complex.I) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hi := congrArg Complex.im hn
  norm_num at hi
  have hnreal : x = (n : ℝ) := by
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    apply (mul_left_cancel₀ (ne_of_gt hp))
    nlinarith [hi]
  have hnpos : 0 < n := by exact_mod_cast (hnreal ▸ hx0)
  have hnlt : n < 1 := by exact_mod_cast (hnreal ▸ hx1)
  omega

private lemma norm_geom_powers_bound {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ B : ℝ, ∀ n : ℕ, ‖∑ i ∈ range n, z ^ (i + 1)‖ ≤ B := by
  refine ⟨2 / ‖z - 1‖, fun n ↦ ?_⟩
  rw [show (∑ i ∈ range n, z ^ (i + 1)) = z * ∑ i ∈ range n, z^i by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ']]
  rw [geom_sum_eq hz1 n, norm_mul, norm_div, hz, one_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  have hn : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  calc
    ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [hn, norm_one]; norm_num

private lemma tendsto_complex_harmonic_twist {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ L : ℂ, Tendsto (fun n : ℕ ↦ ∑ i ∈ range n, z ^ i / (i : ℂ)) atTop (𝓝 L) := by
  obtain ⟨B, hB⟩ := norm_geom_powers_bound hz hz1
  let f : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hfanti : Antitone f := by
    intro m n hmn
    dsimp only [f]
    gcongr
  have hf0 : Tendsto f atTop (𝓝 0) := by
    simpa [f, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc : CauchySeq (fun n ↦ ∑ i ∈ range n, f i • z ^ (i + 1)) :=
    hfanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hB
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, ?_⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  convert hL using 1
  funext n
  rw [sum_range_succ']
  simp only [pow_zero, Nat.cast_zero, div_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp [f, div_eq_mul_inv, smul_eq_mul]
  ring

private lemma complex_harmonic_twist_limit {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (hslit : 1 - z ∈ Complex.slitPlane) {L : ℂ}
    (hL : Tendsto (fun n : ℕ ↦ ∑ i ∈ range n, z ^ i / (i : ℂ)) atTop (𝓝 L)) :
    L = -Complex.log (1 - z) := by
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hL
  have hformula : ∀ r : ℝ, r < 1 → 0 < r →
      (∑' n : ℕ, (z ^ n / (n : ℂ)) * (r : ℂ)^n) =
        -Complex.log (1 - (r : ℂ) * z) := by
    intro r hr hr0
    have hrnorm : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg hr0.le, hz, mul_one]
      exact hr
    have hs := (Complex.hasSum_taylorSeries_neg_log hrnorm).tsum_eq
    rw [← hs]
    apply tsum_congr
    intro n
    rw [mul_pow]
    ring
  have hev : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      (∑' n : ℕ, (z ^ n / (n : ℂ)) * (r : ℂ)^n) =
        -Complex.log (1 - (r : ℂ) * z) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
      with r hr hr0
    exact hformula r hr hr0
  have hc0 : ContinuousAt (fun r : ℝ ↦ (1 : ℂ) - (r : ℂ) * z) 1 := by fun_prop
  have hc : ContinuousAt (fun r : ℝ ↦ -Complex.log (1 - (r : ℂ) * z)) 1 := by
    exact (hc0.clog (by simpa using hslit)).neg
  have hlogfull : Tendsto (fun r : ℝ ↦ -Complex.log (1 - (r : ℂ) * z))
      (𝓝 (1 : ℝ)) (𝓝 (-Complex.log (1-z))) := by
    simpa using hc.tendsto
  have hlog : Tendsto (fun r : ℝ ↦ -Complex.log (1 - (r : ℂ) * z))
      (𝓝[<] (1 : ℝ)) (𝓝 (-Complex.log (1-z))) :=
    hlogfull.mono_left inf_le_left
  have hab' : Tendsto (fun r : ℝ ↦ ∑' n : ℕ,
      (z ^ n / (n : ℂ)) * (r : ℂ)^n) (𝓝[<] (1 : ℝ)) (𝓝 L) := by
    simpa only [tendsto_map'_iff, Function.comp_def, ofReal_one] using hab
  have hevs : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      -Complex.log (1 - (r : ℂ) * z) =
        (∑' n : ℕ, (z ^ n / (n : ℂ)) * (r : ℂ)^n) :=
    hev.mono (fun _ h ↦ h.symm)
  exact tendsto_nhds_unique hab' (hlog.congr' hevs)

private lemma one_sub_exp_factor {θ : ℝ} :
    (1 : ℂ) - Complex.exp (θ * Complex.I) =
      (2 * Real.sin (θ/2) : ℝ) * Complex.exp ((θ/2 - Real.pi/2) * Complex.I) := by
  have hc : ((θ/2 - Real.pi/2 : ℝ) : ℂ) = (θ : ℂ)/2 - (Real.pi : ℂ)/2 := by
    push_cast
    rfl
  rw [← hc]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  apply Complex.ext
  · simp only [sub_re, one_re, add_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im,
      mul_re, ofReal_re, ofReal_im, add_im, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, I_re, I_im, zero_mul, mul_zero, sub_zero]
    rw [Real.cos_sub_pi_div_two]
    rw [show θ = 2 * (θ/2) by ring, Real.cos_two_mul]
    rw [show 2 * (θ/2) / 2 = θ/2 by ring]
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  · simp only [sub_im, one_im, add_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      mul_im, ofReal_re, ofReal_im, add_re, Complex.cos_ofReal_re,
      Complex.sin_ofReal_im, I_re, I_im, zero_mul, mul_zero, mul_one, add_zero, zero_sub]
    rw [Real.sin_sub_pi_div_two]
    rw [show θ = 2 * (θ/2) by ring, Real.sin_two_mul]
    ring

private lemma arg_one_sub_exp {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    Complex.arg (1 - Complex.exp (θ * Complex.I)) = θ/2 - Real.pi/2 := by
  rw [one_sub_exp_factor]
  have hhalf0 : 0 < θ/2 := by linarith
  have hhalfpi : θ/2 < Real.pi := by linarith
  have hs : 0 < 2 * Real.sin (θ/2) :=
    mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hhalf0 hhalfpi)
  rw [Complex.arg_real_mul _ hs]
  have he : Complex.arg (Complex.exp ((θ/2 - Real.pi/2) * Complex.I)) =
      toIocMod Real.two_pi_pos (-Real.pi) (θ/2 - Real.pi/2) := by
    convert Complex.arg_exp_mul_I (θ/2 - Real.pi/2) using 1 <;> push_cast <;> ring
  rw [he]
  apply (toIocMod_eq_self Real.two_pi_pos).2
  constructor <;> dsimp
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

lemma sawtooth_fourier_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ range n,
      Real.sin (2 * Real.pi * k * x) / (k : ℝ)) atTop
      (𝓝 (Real.pi * (1 - 2*x) / 2)) := by
  let z : ℂ := Complex.exp (2 * Real.pi * x * Complex.I)
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_exp]
    simp [z]
  have hz1 : z ≠ 1 := exp_two_pi_I_ne_one hx0 hx1
  obtain ⟨L, hL⟩ := tendsto_complex_harmonic_twist hz hz1
  have harg : Complex.arg (1-z) = 2 * Real.pi * x / 2 - Real.pi / 2 := by
    dsimp only [z]
    have ha := arg_one_sub_exp (θ := 2 * Real.pi * x) (by positivity)
      (by nlinarith [Real.pi_pos])
    convert ha using 1 <;> push_cast <;> ring
  have hslit : 1-z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff_arg.mpr
    constructor
    · rw [harg]
      nlinarith [Real.pi_pos]
    · exact sub_ne_zero.mpr hz1.symm
  have hLeq : L = -Complex.log (1-z) :=
    complex_harmonic_twist_limit hz hz1 hslit hL
  have him : L.im = Real.pi * (1 - 2*x) / 2 := by
    rw [hLeq, neg_im, Complex.log_im]
    rw [harg]
    ring
  have hLim := Complex.continuous_im.tendsto L |>.comp hL
  rw [him] at hLim
  convert hLim using 1
  funext n
  change (∑ k ∈ range n, Real.sin (2 * Real.pi * k * x) / (k : ℝ)) =
    (∑ i ∈ range n, z ^ i / (i : ℂ)).im
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [div_im, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero,
    Complex.normSq_natCast]
  by_cases hk : k = 0
  · subst k; simp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hzpow : z ^ k = Complex.exp ((2 * Real.pi * k * x) * Complex.I) := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexp : Complex.exp ((2 * Real.pi * k * x) * Complex.I) =
      (Real.cos (2 * Real.pi * k * x) : ℂ) +
        (Real.sin (2 * Real.pi * k * x) : ℂ) * Complex.I := by
    convert Complex.exp_mul_I ((2 * Real.pi * k * x : ℝ) : ℂ) using 1 <;>
      push_cast <;> ring
  rw [hzpow, hexp]
  simp only [add_im, ofReal_im, ofReal_re, mul_im, I_im, mul_one, I_re,
    mul_zero, add_zero]
  field_simp
  congr 1
  ring


private lemma norm_sum_range_smul_le {g : ℕ → ℂ} {f : ℕ → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hf0 : ∀ i, 0 ≤ f i) (hanti : Antitone f)
    (hg : ∀ n, ‖∑ i ∈ range n, g i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ range n, f i • g i‖ ≤ B * f 0 := by
  rcases n with _ | n
  · simp only [sum_range_zero, norm_zero]
    exact mul_nonneg hB0 (hf0 0)
  rw [Finset.sum_range_by_parts]
  apply (norm_sub_le _ _).trans
  calc
    ‖f (n + 1 - 1) • ∑ i ∈ range (n+1), g i‖ +
          ‖∑ i ∈ range (n + 1 - 1),
            (f (i + 1) - f i) • ∑ i ∈ range (i + 1), g i‖
      ≤ f n * B + ∑ i ∈ range n, (f i - f (i+1)) * B := by
        simp only [Nat.add_sub_cancel, norm_smul, Real.norm_eq_abs]
        apply add_le_add
        · rw [abs_of_nonneg (hf0 n)]
          exact mul_le_mul_of_nonneg_left (hg _) (hf0 n)
        · apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ i))),
            neg_sub]
          exact mul_le_mul_of_nonneg_left (hg _) (sub_nonneg.mpr (hanti (Nat.le_succ i)))
    _ = B * f 0 := by
      rw [← Finset.sum_mul, Finset.sum_range_sub']
      ring

private lemma sine_shift_partial_bound {θ : ℝ} (hθ :
    Complex.exp (θ * Complex.I) ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m n : ℕ,
      ‖∑ i ∈ range n, (Real.sin (θ * (m+i)) : ℂ)‖ ≤ B := by
  let z := Complex.exp (θ * Complex.I)
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_exp]
    simp [z]
  obtain ⟨B, hB⟩ := norm_geom_powers_bound hz hθ
  refine ⟨B, ?_, fun m n ↦ ?_⟩
  · exact (norm_nonneg _).trans (hB 0)
  have hp : (∑ i ∈ range n, z ^ (m+i)) = z ^ m * ∑ i ∈ range n, z^i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_add]
  have hnorm : ‖∑ i ∈ range n, z ^ (m+i)‖ ≤ B := by
    rw [hp, norm_mul, norm_pow, hz, one_pow, one_mul]
    have heq : (∑ i ∈ range n, z^i) = z⁻¹ * ∑ i ∈ range n, z^(i+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ']
      have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
      field_simp [hz0]
    rw [heq, norm_mul, norm_inv, hz, inv_one, one_mul]
    exact hB n
  have hsum : (∑ i ∈ range n, (Real.sin (θ * (m+i)) : ℂ)) =
      ((∑ i ∈ range n, z^(m+i)).im : ℂ) := by
    rw [Complex.im_sum]
    norm_cast
    apply Finset.sum_congr rfl
    intro i _
    have he : z^(m+i) = Complex.exp ((θ * (m+i)) * Complex.I) := by
      dsimp only [z]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    have hx : Complex.exp ((θ * (m+i)) * Complex.I) =
        (Real.cos (θ*(m+i)) : ℂ) + (Real.sin (θ*(m+i)) : ℂ) * I := by
      convert Complex.exp_mul_I ((θ*(m+i) : ℝ) : ℂ) using 1 <;> push_cast <;> ring
    have hxi := congrArg Complex.im hx
    simpa only [Nat.cast_add, add_im, ofReal_im, ofReal_re, mul_im, I_im, I_re, mul_one,
      mul_zero, add_zero, zero_add] using hxi.symm
  rw [hsum, norm_real]
  exact (abs_im_le_norm _).trans hnorm


private lemma sine_tail_bound {θ B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ m n : ℕ,
      ‖∑ i ∈ range n, (Real.sin (θ * (m+i)) : ℂ)‖ ≤ B)
    {s : ℝ} (hs : 1 ≤ s) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    ‖∑ i ∈ range n, (Real.sin (θ * (m+i)) : ℂ) /
      ((m+i : ℕ) : ℂ) ^ (s : ℂ)‖ ≤ B / m := by
  let f : ℕ → ℝ := fun i ↦ (m+i : ℝ) ^ (-s)
  let g : ℕ → ℂ := fun i ↦ (Real.sin (θ * (m+i)) : ℂ)
  have hf0 (i : ℕ) : 0 ≤ f i := Real.rpow_nonneg (by positivity) _
  have hanti : Antitone f := by
    intro i j hij
    dsimp only [f]
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast hm.trans (Nat.le_add_right m i)
    · exact_mod_cast Nat.add_le_add_left hij m
    · linarith
  have hmain := norm_sum_range_smul_le hB0 hf0 hanti (fun n ↦ hB m n) n
  have heq : (∑ i ∈ range n, (Real.sin (θ * (m+i)) : ℂ) /
      ((m+i : ℕ) : ℂ) ^ (s : ℂ)) = ∑ i ∈ range n, f i • g i := by
    apply Finset.sum_congr rfl
    intro i _
    have hmi : 0 ≤ (m+i : ℝ) := by positivity
    rw [show (((m+i : ℕ) : ℂ) ^ (s : ℂ)) = (((m+i : ℝ)^s : ℝ) : ℂ) by
      simpa using (Complex.ofReal_cpow hmi s).symm]
    simp only [f, g, div_eq_mul_inv, Complex.real_smul, ← ofReal_inv,
      Real.rpow_neg hmi]
    ring
  rw [heq]
  apply hmain.trans
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfbd : f 0 ≤ 1 / (m : ℝ) := by
    dsimp only [f]
    simp only [Nat.cast_add, Nat.cast_zero, add_zero]
    rw [one_div]
    convert Real.rpow_le_rpow_of_exponent_le hmreal (show -s ≤ (-1 : ℝ) by linarith) using 1
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
  simpa [one_div] using mul_le_mul_of_nonneg_left hfbd hB0

private lemma sine_limit_tail_bound {θ B s : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ m n : ℕ,
      ‖∑ i ∈ range n, (Real.sin (θ * (m+i)) : ℂ)‖ ≤ B)
    (hs : 1 ≤ s) {V : ℂ}
    (hlim : Tendsto (fun n : ℕ ↦ ∑ k ∈ range n,
      (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (s : ℂ)) atTop (𝓝 V))
    {m : ℕ} (hm : 1 ≤ m) :
    ‖V - ∑ k ∈ range m, (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (s : ℂ)‖ ≤ B / m := by
  let P := fun n : ℕ ↦ ∑ k ∈ range n,
    (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (s : ℂ)
  have hshift : Tendsto (fun n ↦ P (n+m) - P m) atTop (𝓝 (V-P m)) := by
    exact ((tendsto_add_atTop_iff_nat m).mpr hlim).sub tendsto_const_nhds
  apply le_of_tendsto (tendsto_norm.comp hshift)
  apply Eventually.of_forall
  intro n
  have hid : P (n+m) - P m = ∑ i ∈ range n,
      (Real.sin (θ * (m+i)) : ℂ) / ((m+i : ℕ) : ℂ) ^ (s : ℂ) := by
    dsimp only [P]
    rw [add_comm n m, Finset.sum_range_add, add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i _
    congr 3 <;> push_cast <;> ring
  change ‖P (n+m) - P m‖ ≤ B / m
  rw [hid]
  exact sine_tail_bound hB0 hB hs hm n


lemma sinZeta_one_eq_sawtooth {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HurwitzZeta.sinZeta x 1 = (Real.pi * (1 - 2*x) / 2 : ℝ) := by
  let θ : ℝ := 2 * Real.pi * x
  have hθ : Complex.exp (θ * Complex.I) ≠ 1 := by
    simpa [θ] using exp_two_pi_I_ne_one hx0 hx1
  obtain ⟨B, hB0, hB⟩ := sine_shift_partial_bound hθ
  let u : ℕ → ℝ := fun j ↦ 1 + 1 / (j+1 : ℝ)
  have hu : Tendsto u atTop (𝓝 1) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have huC : Tendsto (fun j ↦ (u j : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa using Complex.continuous_ofReal.tendsto 1 |>.comp hu
  have hu1 (j : ℕ) : 1 < u j := by simp [u]; positivity
  let V : ℕ → ℂ := fun j ↦ HurwitzZeta.sinZeta x (u j)
  have hV : Tendsto V atTop (𝓝 (HurwitzZeta.sinZeta x 1)) := by
    exact (HurwitzZeta.differentiableAt_sinZeta x 1).continuousAt.tendsto.comp huC
  have hseries (j : ℕ) : Tendsto (fun n : ℕ ↦ ∑ k ∈ range n,
      (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (u j : ℂ)) atTop (𝓝 (V j)) := by
    have hs := (HurwitzZeta.hasSum_nat_sinZeta x (s := (u j : ℂ))
      (by simpa using hu1 j)).tendsto_sum_nat
    convert hs using 1
  let S : ℂ := (Real.pi * (1 - 2*x) / 2 : ℝ)
  have hSaw : Tendsto (fun n : ℕ ↦ ∑ k ∈ range n,
      (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (1 : ℂ)) atTop (𝓝 S) := by
    have hs := Complex.continuous_ofReal.tendsto _ |>.comp
      (sawtooth_fourier_limit hx0 hx1)
    convert hs using 1
    funext n
    simp only [Function.comp_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = 0
    · subst k; simp
    · rw [cpow_one]
      push_cast
      dsimp only [θ]
      congr 2 <;> push_cast <;> ring
  have hBlimR : Tendsto (fun t : ℝ ↦ B / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hBlim : Tendsto (fun m : ℕ ↦ B / (m : ℝ)) atTop (𝓝 0) :=
    hBlimR.comp tendsto_natCast_atTop_atTop
  have hVtoS : Tendsto V atTop (𝓝 S) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hevB : ∀ᶠ m : ℕ in atTop, B / (m : ℝ) < ε/3 :=
      hBlim.eventually (Iio_mem_nhds (by linarith))
    have hevS : ∀ᶠ m : ℕ in atTop,
        dist (∑ k ∈ range m, (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (1 : ℂ)) S < ε/3 :=
      (Metric.tendsto_atTop.mp hSaw (ε/3) (by positivity)) |> fun ⟨M,hM⟩ ↦
        Filter.eventually_atTop.2 ⟨M, hM⟩
    obtain ⟨M, ⟨hMB, hM1⟩, hMS⟩ :=
      (hevB.and (eventually_ge_atTop 1) |>.and hevS).exists
    have hhead : Tendsto (fun j ↦ ∑ k ∈ range M,
        (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (u j : ℂ)) atTop
        (𝓝 (∑ k ∈ range M, (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (1 : ℂ))) := by
      apply tendsto_finset_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simp [u]
      · apply Tendsto.div tendsto_const_nhds
          ((tendsto_const_nhds.cpow huC) (by
            apply Complex.mem_slitPlane_iff_arg.mpr
            constructor
            · rw [Complex.natCast_arg]
              exact Real.pi_ne_zero.symm
            · exact_mod_cast hk0))
        simp [hk0]
    obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hhead (ε/3) (by positivity)
    refine ⟨J, fun j hj ↦ ?_⟩
    have htail := sine_limit_tail_bound hB0 hB (le_of_lt (hu1 j)) (hseries j) hM1
    have hheadj := hJ j hj
    calc
      dist (V j) S ≤
          dist (V j) (∑ k ∈ range M, (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (u j : ℂ)) +
          dist (∑ k ∈ range M, (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (u j : ℂ))
            (∑ k ∈ range M, (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (1 : ℂ)) +
          dist (∑ k ∈ range M, (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (1 : ℂ)) S :=
            dist_triangle4 _ _ _ _
      _ < ε := by
        have htail' : dist (V j)
            (∑ k ∈ range M, (Real.sin (θ*k) : ℂ) / (k : ℂ) ^ (u j : ℂ)) ≤ B / (M : ℝ) := by
          simpa [dist_eq_norm] using htail
        linarith
  have := tendsto_nhds_unique hV hVtoS
  simpa [V, S] using this



lemma hurwitzZetaOdd_zero_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) 0 = (1 / 2 - x : ℝ) := by
  have hs (n : ℕ) : (1 : ℂ) ≠ -(n : ℂ) := by
    intro hn
    have hn' := congrArg Complex.re hn
    norm_num at hn'
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have h := HurwitzZeta.hurwitzZetaOdd_one_sub (x : UnitAddCircle)
    (s := (1 : ℂ)) hs
  rw [sinZeta_one_eq_sawtooth hx0 hx1] at h
  norm_num [Complex.cpow_neg, Complex.cpow_one, Complex.Gamma_one,
    Real.pi_ne_zero] at h
  convert h using 1 <;> norm_num [Real.pi_ne_zero] <;>
    field_simp [Real.pi_ne_zero] <;> ring

lemma ZMod.LFunction_zero_of_odd {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ}
    (hΦ : Function.Odd Φ) :
    ZMod.LFunction Φ 0 = -(1 / (N : ℂ)) * ∑ j : ZMod N, (j.val : ℂ) * Φ j := by
  rw [ZMod.LFunction_def_odd hΦ]
  simp only [neg_zero, Complex.cpow_zero, one_mul]
  have hΦ0 : Φ 0 = 0 := by
    have hh := hΦ 0
    simp only [neg_zero] at hh
    apply (mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num))
    linear_combination hh
  calc
    (∑ j : ZMod N, Φ j * HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) 0) =
        ∑ j : ZMod N, Φ j * ((1 / 2 : ℂ) - (j.val : ℂ) / N) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = 0
      · subst j
        simp [hΦ0]
      · rw [ZMod.toAddCircle_apply, hurwitzZetaOdd_zero_of_Ioo]
        · push_cast
          rfl
        · exact div_pos (by exact_mod_cast (ZMod.val_pos.mpr hj))
            (by exact_mod_cast (NeZero.pos N))
        · exact (div_lt_one (Nat.cast_pos.mpr (NeZero.pos N))).2
            (Nat.cast_lt.mpr (ZMod.val_lt j))
    _ = -(1 / (N : ℂ)) * ∑ j : ZMod N, (j.val : ℂ) * Φ j := by
      have hz := hΦ.sum_eq_zero
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hz, zero_mul, zero_sub]
      rw [show -(1 / (N : ℂ)) * (∑ j : ZMod N, (j.val : ℂ) * Φ j) =
        -((1 / (N : ℂ)) * ∑ j : ZMod N, (j.val : ℂ) * Φ j) by ring]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp



