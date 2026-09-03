import Submission.PolynomialMultiplierChirpExclusion

/-! Finite-difference calculus for excluding high-parameter chirps on growing
multiplier ranges. These lemmas do not assert arithmetic correlation cancellation. -/

namespace Erdos371.MultiplicativeChirpObstruction

open Filter Set
open scoped Topology fwdDiff

lemma hasDerivAt_fwdDiff_iter {f g : ℝ → ℝ}
    (hfg : ∀ x : ℝ, 0 < x → HasDerivAt f (g x) x) (r : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt ((fwdDiff (1 : ℝ))^[r] f) ((fwdDiff (1 : ℝ))^[r] g x) x := by
  induction r generalizing x with
  | zero => simpa using hfg x hx
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change HasDerivAt (fun y => ((fwdDiff (1 : ℝ))^[r] f) (y + 1) -
      ((fwdDiff (1 : ℝ))^[r] f) y)
      (((fwdDiff (1 : ℝ))^[r] g) (x + 1) - ((fwdDiff (1 : ℝ))^[r] g) x) x
    convert ((ih (x + 1) (by linarith)).comp x ((hasDerivAt_id x).add_const 1)).sub
      (ih x hx) using 1; simp

/-- Repeated mean value theorem for unit forward differences on the positive
real axis, formulated using an explicit chain of derivatives. -/
theorem fwdDiff_iter_mean_value (F : ℕ → ℝ → ℝ)
    (hF : ∀ r x, 0 < x → HasDerivAt (F r) (F (r + 1) x) x)
    (r : ℕ) (x : ℝ) (hx : 0 < x) :
    ∃ y ∈ Icc x (x + r), ((fwdDiff (1 : ℝ))^[r] (F 0)) x = F r y := by
  induction r generalizing F x with
  | zero => exact ⟨x, by simp, rfl⟩
  | succ r ih =>
    have hd (z : ℝ) (hz : 0 < z) := hasDerivAt_fwdDiff_iter (hF 0) r z hz
    obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope
      ((fwdDiff (1 : ℝ))^[r] (F 0)) ((fwdDiff (1 : ℝ))^[r] (F 1))
      (show x < x + 1 by linarith)
      (fun z hz => (hd z (lt_of_lt_of_le hx hz.1)).continuousAt.continuousWithinAt)
      (fun z hz => hd z (hx.trans hz.1))
    obtain ⟨y, hy, hy'⟩ := ih (fun j => F (j + 1))
      (fun j z hz => hF (j + 1) z hz) z (hx.trans hz.1)
    refine ⟨y, ⟨by linarith [hy.1, hz.1], by push_cast; linarith [hy.2, hz.2]⟩, ?_⟩
    rw [Function.iterate_succ_apply']
    change ((fwdDiff (1 : ℝ))^[r] (F 0)) (x + 1) - ((fwdDiff (1 : ℝ))^[r] (F 0)) x = _
    have he' : ((fwdDiff (1 : ℝ))^[r] (F 1)) z =
        ((fwdDiff (1 : ℝ))^[r] (F 0)) (x + 1) - ((fwdDiff (1 : ℝ))^[r] (F 0)) x := by
      simpa using he
    exact he'.symm.trans hy'

noncomputable def logDerivativeChain : ℕ → ℝ → ℝ
  | 0 => Real.log
  | r + 1 => fun x => ((-1 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (-((r : ℤ) + 1))

lemma logDerivativeChain_hasDerivAt (r : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (logDerivativeChain r) (logDerivativeChain (r + 1) x) x := by
  cases r with
  | zero => simpa [logDerivativeChain] using Real.hasDerivAt_log hx.ne'
  | succ r =>
    have hd := (hasDerivAt_zpow (-((r : ℤ) + 1)) x (Or.inl hx.ne')).const_mul
      ((-1 : ℝ) ^ r * (r.factorial : ℝ))
    convert hd using 1
    simp only [logDerivativeChain, Nat.cast_add, Nat.cast_one, Int.cast_neg,
      Int.cast_add, Int.cast_natCast, Int.cast_one, pow_succ, Nat.factorial_succ,
      Nat.cast_mul]
    ring_nf

/-- Exact mean-value representation of a logarithmic forward difference. -/
theorem log_fwdDiff_mean_value (r : ℕ) (x : ℝ) (hx : 0 < x) :
    ∃ y ∈ Icc x (x + (r + 1 : ℕ)),
      ((fwdDiff (1 : ℝ))^[r + 1] Real.log) x =
        ((-1 : ℝ) ^ r * (r.factorial : ℝ)) / y ^ (r + 1) := by
  obtain ⟨y, hy, he⟩ := fwdDiff_iter_mean_value logDerivativeChain
    logDerivativeChain_hasDerivAt (r + 1) x hx
  refine ⟨y, hy, ?_⟩
  simpa only [logDerivativeChain, ← Int.natCast_add_one, zpow_neg,
    zpow_natCast, div_eq_mul_inv] using he

set_option linter.style.existsImplication false in
/-- The leading asymptotic of each nonzero-order logarithmic difference. -/
theorem tendsto_scaled_log_fwdDiff (r : ℕ) :
    Tendsto (fun x : ℝ => x ^ (r + 1) * ((fwdDiff (1 : ℝ))^[r + 1] Real.log) x)
      atTop (nhds ((-1 : ℝ) ^ r * (r.factorial : ℝ))) := by
  have hex (x : ℝ) : ∃ y : ℝ, 0 < x →
      y ∈ Icc x (x + (r + 1 : ℕ)) ∧
      ((fwdDiff (1 : ℝ))^[r + 1] Real.log) x =
        ((-1 : ℝ) ^ r * (r.factorial : ℝ)) / y ^ (r + 1) := by
    by_cases hx : 0 < x
    · obtain ⟨y, hy, he⟩ := log_fwdDiff_mean_value r x hx
      exact ⟨y, fun _ => ⟨hy, he⟩⟩
    · exact ⟨1, fun h => (hx h).elim⟩
  choose y hy using hex
  have hrat : Tendsto (fun x : ℝ => y x / x) atTop (nhds 1) := by
    have hupper : Tendsto (fun x : ℝ => 1 + (r + 1 : ℕ) / x) atTop (nhds 1) := by
      simpa [div_eq_mul_inv] using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ((r + 1 : ℕ) : ℝ)).const_add 1
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact (le_div_iff₀ hx).mpr (by simpa using (hy x hx).1.1)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      apply (div_le_iff₀ hx).mpr
      have hh := (hy x hx).1.2
      field_simp
      nlinarith
  have ht := (((hrat.inv₀ one_ne_zero).pow (r + 1)).const_mul
    ((-1 : ℝ) ^ r * (r.factorial : ℝ)))
  simp only [inv_one, one_pow, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [(hy x hx).2, inv_div, div_pow]
  ring

noncomputable def phaseExp (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)

lemma phaseExp_sub (t x y : ℝ) :
    phaseExp t (x - y) = phaseExp t x / phaseExp t y := by
  unfold phaseExp
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

lemma phaseExp_log_nat (t : ℝ) (k : ℕ) (hk : k ≠ 0) :
    phaseExp t (Real.log k) = chirp t k := (chirp_apply t k hk).symm

lemma tendsto_phaseExp_fwdDiff (t : ℕ → ℝ) (k : ℕ → ℕ)
    (h : ∀ s : ℕ, Tendsto (fun j => phaseExp (t j) (Real.log (k j + s : ℕ)))
      atTop (nhds 1)) (r : ℕ) :
    Tendsto (fun j => phaseExp (t j)
      (((fwdDiff (1 : ℝ))^[r] Real.log) (k j))) atTop (nhds 1) := by
  induction r generalizing k with
  | zero => simpa using h 0
  | succ r ih =>
    have hshift : ∀ s : ℕ, Tendsto
        (fun j => phaseExp (t j) (Real.log ((k j + 1) + s : ℕ))) atTop (nhds 1) := by
      intro s
      simpa only [Nat.add_assoc, Nat.add_comm 1 s] using h (s + 1)
    have ht := (ih (fun j => k j + 1) hshift).div (ih k h) one_ne_zero
    simp only [div_self one_ne_zero] at ht
    convert ht using 1
    ext j
    rw [Function.iterate_succ_apply']
    simp only [fwdDiff, phaseExp_sub, Nat.cast_add, Nat.cast_one, Pi.div_apply]

lemma phaseExp_integer_ne_one (m : ℤ) (hm : m ≠ 0) : phaseExp 1 m ≠ 1 := by
  intro he
  have hs : Real.sin (m : ℝ) = 0 := by
    have hh := congrArg Complex.im he
    simpa only [phaseExp, one_mul, Complex.exp_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, Real.exp_zero,
      Complex.one_im] using hh
  obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hs
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp only [Int.cast_zero, zero_mul] at hz
    exact hm (Int.cast_eq_zero.mp hz.symm)
  exact (irrational_pi.intCast_mul hz0).ne_int m hz

/-- Resonance on every fixed translate of a multiplier sequence is
impossible when the parameter grows like a positive integral power of it. -/
theorem no_consecutive_resonance_at_power_scale (r : ℕ)
    (a : ℕ → ℝ) (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (hscale : Tendsto (fun j => a j / (k j : ℝ) ^ (r + 1)) atTop (nhds 1)) :
    ¬ (∀ s : ℕ, Tendsto (fun j => phaseExp (a j) (Real.log (k j + s : ℕ)))
      atTop (nhds 1)) := by
  intro h
  let c : ℝ := (-1 : ℝ) ^ r * (r.factorial : ℝ)
  have hk' : Tendsto (fun j => (k j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have ht0 := hscale.mul ((tendsto_scaled_log_fwdDiff r).comp hk')
  have ht : Tendsto (fun j => a j * ((fwdDiff (1 : ℝ))^[r + 1] Real.log) (k j))
      atTop (nhds c) := by
    simp only [one_mul] at ht0
    apply ht0.congr'
    filter_upwards [hk.eventually_gt_atTop 0] with j hj
    have hn : (k j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
    dsimp
    field_simp
  have hc : Continuous (fun x : ℝ => phaseExp 1 x) := by unfold phaseExp; fun_prop
  have ht' : Tendsto (fun j => phaseExp (a j)
      (((fwdDiff (1 : ℝ))^[r + 1] Real.log) (k j))) atTop (nhds (phaseExp 1 c)) := by
    simpa only [Function.comp_def, phaseExp, one_mul] using (hc.tendsto c).comp ht
  have he := tendsto_nhds_unique ht' (tendsto_phaseExp_fwdDiff a k h (r + 1))
  have hm : (-1 : ℤ) ^ r * (r.factorial : ℤ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero r)
  apply phaseExp_integer_ne_one _ hm
  simpa only [c, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] using he

/-- No unbounded subsequence of the biased chirps is uniformly close to one
on every multiplier up to any fixed positive power of its parameter. -/
theorem no_uniform_power_multiplier_invariance (δ : ℝ) (hδ : 0 < δ)
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∀ m : ℕ,
      0 < m → (m : ℝ) ≤ (a j : ℝ) ^ δ → ‖chirp (a j) m - 1‖ < ε) := by
  intro h
  obtain ⟨r, hr⟩ := exists_nat_one_div_lt hδ
  let d : ℕ := r + 1
  have hd : d ≠ 0 := by dsimp [d]; omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  have hdinv : (d : ℝ)⁻¹ < δ := by simpa only [one_div, Nat.cast_add, Nat.cast_one, d] using hr
  let u : ℕ → ℝ := fun j => (a j : ℝ) ^ (d : ℝ)⁻¹
  let k : ℕ → ℕ := fun j => ⌊u j⌋₊
  have ha' : Tendsto (fun j => (a j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp ha
  have hu : Tendsto u atTop atTop := (tendsto_rpow_atTop (inv_pos.mpr hdpos)).comp ha'
  have hk : Tendsto k atTop atTop := tendsto_nat_floor_atTop.comp hu
  have hupow (j : ℕ) : (u j) ^ d = (a j : ℝ) :=
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) hd
  have hfrac : Tendsto (fun j => (k j : ℝ) ^ d / (a j : ℝ)) atTop (nhds 1) := by
    have ht := (tendsto_nat_floor_div_atTop.comp hu).pow d
    simpa only [Function.comp_def, div_pow, hupow, one_pow] using ht
  have hscale : Tendsto (fun j => (a j : ℝ) / (k j : ℝ) ^ (r + 1)) atTop (nhds 1) := by
    simpa only [inv_div, inv_one, d] using hfrac.inv₀ one_ne_zero
  apply no_consecutive_resonance_at_power_scale r (fun j => (a j : ℝ)) k hk hscale
  intro s
  have hratio : Tendsto (fun j => (a j : ℝ) ^ (δ - (d : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hdinv)).comp ha'
  have hbound : ∀ᶠ j : ℕ in atTop, ((k j + s : ℕ) : ℝ) ≤ (a j : ℝ) ^ δ := by
    filter_upwards [hu.eventually_ge_atTop (s : ℝ), hratio.eventually_ge_atTop 2,
      ha.eventually_gt_atTop 0] with j huj hrj haj
    have hapos : (0 : ℝ) < a j := by exact_mod_cast haj
    have hunonneg : 0 ≤ u j := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc
      ((k j + s : ℕ) : ℝ) = (k j : ℝ) + s := by push_cast; rfl
      _ ≤ u j + s := add_le_add (Nat.floor_le hunonneg) le_rfl
      _ ≤ 2 * u j := by linarith
      _ ≤ u j * (a j : ℝ) ^ (δ - (d : ℝ)⁻¹) := by nlinarith
      _ = (a j : ℝ) ^ δ := by
        dsimp [u]
        rw [← Real.rpow_add hapos]
        congr 1
        ring
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h ε hε, hbound, hk.eventually_gt_atTop 0] with j hj hb hk0
  rw [phaseExp_log_nat _ _ (by omega : k j + s ≠ 0), dist_eq_norm]
  exact hj (k j + s) (by omega) hb

/-- A uniform positive separation holds eventually on every positive-power
multiplier range. The separation constant may depend on the exponent. -/
theorem eventual_power_multiplier_separation (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ (N : ℝ) ^ δ ∧ ε ≤ ‖chirp N m - 1‖ := by
  suffices ∃ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ (N : ℝ) ^ δ ∧ ε ≤ ‖chirp N m - 1‖ by
    obtain ⟨ε, hε, N₀, hN₀⟩ := this
    exact ⟨ε, hε, eventually_atTop.mpr ⟨N₀, hN₀⟩⟩
  by_contra! h
  have hh (j : ℕ) := h (1 / (j + 1 : ℝ)) (by positivity) j
  choose a ha hsmall using hh
  have hat : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
  apply no_uniform_power_multiplier_invariance δ hδ a hat
  intro ε hε
  have he := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε
  filter_upwards [he] with j hj
  intro m hm hb
  exact (hsmall j m hm hb).trans hj

#print axioms log_fwdDiff_mean_value
#print axioms tendsto_scaled_log_fwdDiff
#print axioms tendsto_phaseExp_fwdDiff
#print axioms phaseExp_integer_ne_one
#print axioms no_consecutive_resonance_at_power_scale
#print axioms no_uniform_power_multiplier_invariance
#print axioms eventual_power_multiplier_separation

end Erdos371.MultiplicativeChirpObstruction
