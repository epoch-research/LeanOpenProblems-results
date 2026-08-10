import FormalConjectures.Util.ProblemImports

open Finset Complex Real Filter
open scoped Real Topology

/-- Gaussian summability over `ℤ`. -/
lemma summable_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℤ => Real.exp (-c * m ^ 2)) := by
  have him : (0:ℝ) < ((c/π : ℝ) * Complex.I).im := by
    simp [Complex.mul_im]; positivity
  have hsum := (summable_jacobiTheta₂_term_iff (0:ℂ) ((c/π : ℝ) * Complex.I)).mpr him
  rw [← summable_norm_iff] at hsum
  refine hsum.congr (fun m => ?_)
  rw [jacobiTheta₂_term, Complex.norm_exp]
  rw [show (2 * π * I * m * 0 + π * I * m ^ 2 * ((c/π : ℝ) * Complex.I)) = (((-c * m ^ 2 : ℝ)):ℂ) by
    push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring]
  exact (Complex.ofReal_re _).symm ▸ rfl

/-- Norm of the dual theta term. -/
lemma dual_term_norm (t : ℝ) (ht : 0 < t) (x : ℝ) (m : ℤ) :
    ‖Complex.exp (-π * m ^ 2 / t) * Complex.exp (2 * π * I * m * x)‖ = Real.exp (-π * m ^ 2 / t) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  have h1 : (-(π:ℂ) * m ^ 2 / t).re = -π * m ^ 2 / t := by
    rw [show (-(π:ℂ) * m ^ 2 / t) = (((-π * m ^ 2 / t : ℝ)):ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have h2 : (2 * (π:ℂ) * I * m * x).re = 0 := by
    rw [show (2 * (π:ℂ) * I * m * x) = ((2*π*m*x : ℝ):ℂ) * I by push_cast; ring]
    simp
  rw [h1, h2, Real.exp_zero, mul_one]

/-- Summability of the dual theta term norms. -/
lemma summable_dual_norm (t : ℝ) (ht : 0 < t) (x : ℝ) :
    Summable (fun m : ℤ => ‖Complex.exp (-π * m ^ 2 / t) * Complex.exp (2 * π * I * m * x)‖) := by
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => le_of_eq (dual_term_norm t ht x m))
  -- ∑ exp(-πm²/t) summable. Compare to jacobiTheta₂ term summability.
  have : (0:ℝ) < (Complex.I / t).im := by simp [Complex.div_im, ht]
  have hsum := (summable_jacobiTheta₂_term_iff (0:ℂ) (Complex.I / t)).mpr this
  rw [← summable_norm_iff] at hsum
  refine hsum.congr (fun m => ?_)
  rw [jacobiTheta₂_term, Complex.norm_exp]
  congr 1
  rw [show (2 * π * I * m * 0 + π * I * m ^ 2 * (Complex.I / t)) = (((-π * m ^ 2 / t : ℝ)):ℂ) by
    push_cast; rw [div_eq_mul_inv]; ring_nf; rw [Complex.I_sq]; ring]
  exact Complex.ofReal_re _

/-- The dual theta sum `g(t,x) := ∑ₘ exp(-πm²/t) exp(2πImx)` tends to `1` as `t → 0⁺`. -/
theorem dual_theta_tendsto_one (x : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => ∑' m : ℤ, Complex.exp (-π * m ^ 2 / t) * Complex.exp (2 * π * I * m * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hlim : (1 : ℂ) = ∑' m : ℤ, (if m = 0 then (1:ℂ) else 0) := (tsum_ite_eq 0 1).symm
  rw [hlim]
  apply tendsto_tsum_of_dominated_convergence (bound := fun m : ℤ => Real.exp (-π * m ^ 2))
  · exact summable_exp_neg_mul_sq Real.pi_pos
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, zero_div, neg_zero, Complex.exp_zero, mul_zero, one_mul, if_pos]
      simpa using tendsto_const_nhds
    · simp only [if_neg hm]
      have hc : 0 < π * (m:ℝ) ^ 2 := by
        have : (m:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
        positivity
      have hinv : Filter.Tendsto (fun t : ℝ => t⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
        tendsto_inv_nhdsGT_zero
      have h2 : Filter.Tendsto (fun t : ℝ => π * (m:ℝ) ^ 2 * t⁻¹) (nhdsWithin 0 (Set.Ioi 0))
          Filter.atTop := hinv.const_mul_atTop hc
      have h3 : Filter.Tendsto (fun t : ℝ => -π * (m:ℝ) ^ 2 / t) (nhdsWithin 0 (Set.Ioi 0))
          Filter.atBot := by
        have := tendsto_neg_atTop_atBot.comp h2
        refine this.congr (fun t => ?_)
        simp only [Function.comp_apply]; ring
      have h4 : Filter.Tendsto (fun t : ℝ => Real.exp (-π * (m:ℝ) ^ 2 / t))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := Real.tendsto_exp_atBot.comp h3
      have h5 : Filter.Tendsto (fun t : ℝ => Complex.exp (-π * (m:ℂ) ^ 2 / t))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hcomp := (Complex.continuous_ofReal.tendsto 0).comp h4
        simp only [Complex.ofReal_zero] at hcomp
        refine hcomp.congr (fun t => ?_)
        rw [Function.comp_apply, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      have : (0:ℂ) = Complex.exp (2 * π * I * m * x) * 0 := by ring
      rw [this]
      exact (h5.const_mul _).congr (fun t => by ring)
  · have h_lt1 : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
      Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))
        (fun t ht => ht)
    filter_upwards [self_mem_nhdsWithin, h_lt1] with t ht0 ht1 m
    rw [dual_term_norm t ht0 x m, Real.exp_le_exp]
    have ht0' : (0:ℝ) < t := ht0
    have hmsq : (0:ℝ) ≤ (m:ℝ) ^ 2 := sq_nonneg _
    rw [div_le_iff₀ ht0']
    have hp : (0:ℝ) ≤ π * (m:ℝ) ^ 2 := mul_nonneg Real.pi_pos.le hmsq
    nlinarith [mul_nonneg hp (by linarith : (0:ℝ) ≤ 1 - t)]

/-- Complex version of the theta transformation, the cleaner object to work with. -/
theorem theta_complex_transform (α : ℝ) (hα : 0 < α) (x : ℝ) :
    (∑' m : ℤ, Complex.exp (-(α:ℂ) * (m + x) ^ 2)) =
      Real.sqrt (π / α) * ∑' m : ℤ, Complex.exp (-π ^ 2 * m ^ 2 / α)
        * Complex.exp (2 * π * I * m * x) := by
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hα' : (α:ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have ha : 0 < ((α:ℂ)/π).re := by
    rw [div_re]; simp [Complex.normSq]; positivity
  have key := Complex.tsum_exp_neg_quadratic ha (-(α*x)/π : ℝ)
  -- Step 1: rewrite LHS as cexp(-αx²) * (key's LHS sum)
  have hL : (∑' m : ℤ, Complex.exp (-(α:ℂ) * (m + x) ^ 2)) =
      Complex.exp (-(α:ℂ)*x^2) *
        ∑' m : ℤ, Complex.exp (-π * ((α:ℂ)/π) * m ^ 2 + 2 * π * ((-(α*x)/π : ℝ):ℂ) * m) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [hL, key]
  -- Step 2: simplify constant and RHS sum
  have hconst : (1 : ℂ) / ((α:ℂ)/π) ^ (1/2 : ℂ) = (Real.sqrt (π/α) : ℂ) := by
    rw [show ((α:ℂ)/π) = (((α/π : ℝ)):ℂ) by push_cast; ring,
        show (1/2 : ℂ) = (((1/2 : ℝ)):ℂ) by norm_num,
        ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_one, ← Complex.ofReal_div]
    rw [Real.sqrt_eq_rpow]
    congr 1
    rw [one_div, ← Real.inv_rpow (by positivity), inv_div]
  -- Now combine the cexp(-αx²) constant with the sum
  rw [hconst, mul_left_comm]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hb : ((-(α*x)/π : ℝ):ℂ) = -((α:ℂ)*x)/π := by push_cast; ring
  rw [hb]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The shifted theta tends to `1/√t`-scaled: `√t·∑ₘ exp(-πt(m+x)²) → 1`. -/
theorem shifted_theta_asymp (x : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => (Real.sqrt t : ℂ) * ∑' m : ℤ, Complex.exp (-(π * t : ℝ) * (m + x) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have key : ∀ t : ℝ, 0 < t →
      (Real.sqrt t : ℂ) * ∑' m : ℤ, Complex.exp (-(π * t : ℝ) * (m + x) ^ 2) =
        ∑' m : ℤ, Complex.exp (-π * m ^ 2 / t) * Complex.exp (2 * π * I * m * x) := by
    intro t ht
    have he : ((π * t : ℝ) : ℂ) = ((π * t : ℝ) : ℂ) := rfl
    rw [show (fun m : ℤ => Complex.exp (-(π * t : ℝ) * (m + x) ^ 2))
          = (fun m : ℤ => Complex.exp (-((π*t:ℝ):ℂ) * (m + x) ^ 2)) from rfl]
    rw [theta_complex_transform (π * t) (by positivity) x, ← mul_assoc]
    have hsqrt : (Real.sqrt t : ℂ) * (Real.sqrt (π / (π * t)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul ht.le,
        show t * (π / (π * t)) = 1 by field_simp]
      simp
    rw [hsqrt, one_mul]
    refine tsum_congr (fun m => ?_)
    congr 1
    congr 1
    push_cast
    field_simp
  apply Filter.Tendsto.congr' _ (dual_theta_tendsto_one x)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (key t ht).symm

/-- The classical quadratic Gauss sum `g(N) = ∑_{k<N} exp(2πik²/N)`. -/
noncomputable def gaussSumC (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N)

/-- The regularized theta `G(N,ε) = ∑_{n∈ℤ} exp(-π(ε - 2i/N)n²)`. -/
noncomputable def Gtheta (N : ℕ) (ε : ℝ) : ℂ :=
  ∑' n : ℤ, Complex.exp (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2)

/-- Norm of the regularized theta term. -/
lemma Greg_term_norm (N : ℕ) (ε : ℝ) (n : ℤ) :
    ‖Complex.exp (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2)‖ = Real.exp (-(π * ε) * n ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  have : (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2)
      = (((-(π*ε)*n^2 : ℝ)):ℂ) + (2 * π / N * n ^ 2 : ℝ) * I := by
    push_cast; ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
  ring

/-- Summability of the regularized theta term. -/
lemma summable_Greg (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℤ => Complex.exp (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2)) := by
  rw [← summable_norm_iff]
  apply (summable_exp_neg_mul_sq (c := π * ε) (by positivity)).congr
  intro n
  rw [Greg_term_norm]

/-- Period-N regrouping of the regularized theta. -/
theorem Gtheta_decomp (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    Gtheta N ε = ∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) *
      ∑' m : ℤ, Complex.exp (-(π * ε : ℝ) * (k + N * m) ^ 2) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  set F : ℤ → ℂ := fun n => Complex.exp (-(π:ℂ) * ((ε:ℂ) - 2 * I / N) * n ^ 2) with hF
  have hsum : Summable F := summable_Greg N hN ε hε
  have hsum2 : Summable (fun p : ℤ × Fin N => F ((Int.divModEquiv N).symm p)) :=
    hsum.comp_injective (Int.divModEquiv N).symm.injective
  -- term identity: F(q*N + r) = exp(2πi r²/N) · exp(-(πε)(r+Nq)²)
  have hterm : ∀ (q : ℤ) (r : Fin N),
      F ((Int.divModEquiv N).symm (q, r)) =
        Complex.exp (2 * π * I * (r:ℕ) ^ 2 / N) *
          Complex.exp (-(π * ε : ℝ) * ((r:ℕ) + N * q) ^ 2) := by
    intro q r
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hsymm : (Int.divModEquiv N).symm (q, r) = q * (N:ℤ) + (r:ℕ) := rfl
    rw [show Complex.exp (2 * π * I * (r:ℕ) ^ 2 / N)
            * Complex.exp (-(π * ε : ℝ) * ((r:ℕ) + N * q) ^ 2)
          = Complex.exp (2 * π * I * (r:ℕ) ^ 2 / N + -(π * ε : ℝ) * ((r:ℕ) + N * q) ^ 2)
        from (Complex.exp_add _ _).symm]
    rw [hF]
    simp only [hsymm]
    rw [show (((q * (N:ℤ) + (r:ℕ) : ℤ)):ℂ) = (q:ℂ) * N + (r:ℕ) from by push_cast; ring]
    rw [show -(π:ℂ) * ((ε:ℂ) - 2 * I / N) * ((q:ℂ) * N + (r:ℕ)) ^ 2
          = (2 * π * I * (r:ℕ) ^ 2 / N + -(π * ε : ℝ) * ((r:ℕ) + N * q) ^ 2)
            + ((q ^ 2 * N + 2 * q * (r:ℕ) : ℤ) : ℂ) * (2 * π * I)
        from by push_cast; field_simp [hNc]; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- regroup via n = q*N + r
  unfold Gtheta
  rw [← hF, ← (Int.divModEquiv N).symm.tsum_eq F]
  rw [hsum2.tsum_prod' (fun q => (hasSum_fintype
        (fun r : Fin N => F ((Int.divModEquiv N).symm (q, r)))).summable)]
  simp_rw [tsum_fintype]
  rw [Summable.tsum_finsetSum (fun r _ => ?_)]
  · -- reindex Fin N → range N
    rw [← Fin.sum_univ_eq_sum_range (fun k => Complex.exp (2 * π * I * k ^ 2 / N) *
          ∑' m : ℤ, Complex.exp (-(π * ε : ℝ) * (k + N * m) ^ 2))]
    apply Finset.sum_congr rfl
    intro r _
    rw [← tsum_mul_left]
    refine tsum_congr (fun q => ?_)
    rw [hterm q r]
  · -- summability of q ↦ F(symm(q,r)) for fixed r
    exact hsum2.comp_injective (fun a b h => by simpa using h)

-- The LHS limit: `√ε · Gtheta(N,ε) → gaussSumC(N)/N` as `ε → 0⁺`.
set_option maxHeartbeats 1000000 in
theorem sqrt_eps_Gtheta_limit (N : ℕ) (hN : 0 < N) :
    Filter.Tendsto (fun ε : ℝ => (Real.sqrt ε : ℂ) * Gtheta N ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (gaussSumC N / N)) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNr' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  -- ε ↦ ε·N² maps the punctured nbhd to itself
  have htN : Filter.Tendsto (fun ε : ℝ => ε * (N:ℝ) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Filter.Tendsto (fun ε : ℝ => ε * (N:ℝ) ^ 2) (nhds 0) (nhds 0) := by
        have := (continuous_mul_right ((N:ℝ) ^ 2)).tendsto 0; simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : 0 < ε := hε
      exact mul_pos hε' (by positivity)
  -- for each k, the inner shifted theta (scaled) tends to 1
  have hk : ∀ k : ℕ,
      Filter.Tendsto (fun ε : ℝ => (Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) *
        ∑' m : ℤ, Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * (m + (k:ℝ) / N) ^ 2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    intro k
    refine Filter.Tendsto.congr (fun ε => ?_) ((shifted_theta_asymp ((k:ℝ) / N)).comp htN)
    simp only [Function.comp_apply]
    refine congrArg (HMul.hMul (Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ)) (tsum_congr (fun m => ?_))
    congr 1
    push_cast
    ring
  -- inner term identity
  have hinner : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ,
      (Real.sqrt ε : ℂ) * ∑' m : ℤ, Complex.exp (-(π * ε : ℝ) * (k + N * m) ^ 2) =
        (1 / N) * ((Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) *
          ∑' m : ℤ, Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * (m + (k:ℝ) / N) ^ 2)) := by
    intro ε hε k
    have hcoef : (Real.sqrt ε : ℂ) = (1 / N) * (Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) := by
      rw [Real.sqrt_mul hε.le, Real.sqrt_sq hNr.le, Complex.ofReal_mul,
        Complex.ofReal_natCast]
      field_simp
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    have hA : Complex.exp (-(π * ε : ℝ) * ((k:ℂ) + N * m) ^ 2) =
        Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * ((m:ℂ) + (k:ℝ) / N) ^ 2) := by
      congr 1
      push_cast
      field_simp
      ring
    rw [hA, hcoef]
    ring
  -- rewrite √ε·Gtheta as a finite sum of these
  have hrw : ∀ ε : ℝ, 0 < ε →
      (Real.sqrt ε : ℂ) * Gtheta N ε =
        ∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) *
          ((1 / N) * ((Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) *
            ∑' m : ℤ, Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * (m + (k:ℝ) / N) ^ 2))) := by
    intro ε hε
    rw [Gtheta_decomp N hN ε hε, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm, hinner ε hε k]
  -- conclude
  have hlim : Filter.Tendsto
      (fun ε : ℝ => ∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) *
          ((1 / N) * ((Real.sqrt (ε * (N:ℝ) ^ 2) : ℂ) *
            ∑' m : ℤ, Complex.exp (-(π * (ε * (N:ℝ) ^ 2) : ℝ) * (m + (k:ℝ) / N) ^ 2))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) * ((1 / N) * 1))) := by
    apply tendsto_finset_sum
    intro k _
    exact (((hk k).const_mul ((1:ℂ) / N)).const_mul (Complex.exp (2 * π * I * k ^ 2 / N)))
  have heq : (∑ k ∈ Finset.range N, Complex.exp (2 * π * I * k ^ 2 / N) * ((1 / N) * 1))
      = gaussSumC N / N := by
    unfold gaussSumC
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_one]
    field_simp
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hrw ε hε).symm

-- Complex shifted theta limit: if `s ε → 0` with `Re(s ε) > 0` and `Re(1/s ε) → ∞`,
-- then `(s ε)^{1/2} · ∑ₘ exp(-π s ε (m+x)²) → 1`. Complex analogue of `shifted_theta_asymp`.
set_option maxHeartbeats 1000000 in
theorem complex_shifted_theta (x : ℝ) (l : Filter ℝ) (s : ℝ → ℂ)
    (hs : Filter.Tendsto s l (nhds 0)) (hre : ∀ᶠ ε in l, 0 < (s ε).re)
    (hdom : Filter.Tendsto (fun ε => (s ε).re / Complex.normSq (s ε)) l Filter.atTop) :
    Filter.Tendsto (fun ε => (s ε) ^ (1/2 : ℂ) *
        ∑' m : ℤ, Complex.exp (-π * (s ε) * (m + x) ^ 2)) l (nhds 1) := by
  -- Poisson transform pointwise (where Re(s ε) > 0)
  have key : ∀ᶠ ε in l, (s ε) ^ (1/2 : ℂ) *
        ∑' m : ℤ, Complex.exp (-π * (s ε) * (m + x) ^ 2)
      = Complex.exp (-π * (s ε) * x ^ 2) *
          ∑' n : ℤ, Complex.exp (-π / (s ε) * (n - I * (s ε) * x) ^ 2) := by
    filter_upwards [hre] with ε hε
    have hP := Complex.tsum_exp_neg_quadratic hε (-(s ε) * x)
    -- ∑ exp(-π s m² + 2π(-s x) m) = 1/s^{1/2} ∑ exp(-π/s (n + I(-s x))²)
    have hLHS : ∑' m : ℤ, Complex.exp (-π * (s ε) * (m + x) ^ 2)
        = Complex.exp (-π * (s ε) * x ^ 2) *
          ∑' m : ℤ, Complex.exp (-π * (s ε) * m ^ 2 + 2 * π * (-(s ε) * x) * m) := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun m => ?_)
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hLHS, hP]
    rw [mul_comm ((s ε) ^ (1/2 : ℂ)), mul_assoc]
    congr 1
    rw [mul_comm, ← mul_assoc]
    rw [show (s ε) ^ (1/2 : ℂ) * (1 / (s ε) ^ (1/2 : ℂ)) = 1 from ?_, one_mul]
    · refine tsum_congr (fun n => ?_)
      congr 2
      ring
    · rw [mul_one_div, div_self]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      intro h0
      rw [h0] at hε
      simp at hε
  rw [tendsto_congr' key]
  -- limit of product: exp(-π s x²) → 1, dual sum → 1
  have h1 : Filter.Tendsto (fun ε => Complex.exp (-π * (s ε) * x ^ 2)) l (nhds 1) := by
    have : Filter.Tendsto (fun ε => -π * (s ε) * x ^ 2) l (nhds 0) := by
      have := (hs.const_mul (-(π:ℂ))).mul_const ((x:ℂ) ^ 2)
      simpa using this
    have hc := (Complex.continuous_exp.tendsto 0).comp this
    simpa using hc
  have hre0 : Filter.Tendsto (fun ε => (s ε).re) l (nhds 0) :=
    (Complex.continuous_re.tendsto 0).comp hs
  -- norm of the dual term
  have hnorm : ∀ n : ℤ, ∀ ε, 0 < (s ε).re →
      ‖Complex.exp (-π / (s ε) * (n - I * (s ε) * x) ^ 2)‖
      = Real.exp (-π * n ^ 2 * ((s ε).re / Complex.normSq (s ε)) + π * x ^ 2 * (s ε).re) := by
    intro n ε hε
    have hsne : s ε ≠ 0 := fun h => by rw [h] at hε; simp at hε
    rw [Complex.norm_exp]
    congr 1
    rw [show -π / (s ε) * ((n:ℂ) - I * (s ε) * x) ^ 2
          = ((-π * (n:ℝ) ^ 2 : ℝ):ℂ) * (s ε)⁻¹ + ((2 * π * (n:ℝ) * x : ℝ):ℂ) * I
            + ((π * x ^ 2 : ℝ):ℂ) * (s ε) by
        field_simp
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring]
    rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
        Complex.re_ofReal_mul, Complex.inv_re]
    simp only [Complex.I_re, mul_zero, add_zero]
  have h2 : Filter.Tendsto
      (fun ε => ∑' n : ℤ, Complex.exp (-π / (s ε) * (n - I * (s ε) * x) ^ 2)) l (nhds 1) := by
    have hbound : Summable (fun n : ℤ => Real.exp (π * x ^ 2) * Real.exp (-π * n ^ 2)) :=
      (summable_exp_neg_mul_sq Real.pi_pos).mul_left _
    rw [show (1 : ℂ) = ∑' n : ℤ, (if n = 0 then (1:ℂ) else 0) from (tsum_ite_eq 0 1).symm]
    apply tendsto_tsum_of_dominated_convergence hbound
    · -- pointwise limits
      intro n
      by_cases hn : n = 0
      · subst hn
        simp only [↓reduceIte]
        have hlim0 : Filter.Tendsto
            (fun ε => -π / (s ε) * ((0:ℤ) - I * (s ε) * x) ^ 2) l (nhds 0) := by
          have heq2 : (fun ε => -π / (s ε) * ((0:ℤ) - I * (s ε) * x) ^ 2)
              = (fun ε => π * (s ε) * x ^ 2) := by
            funext ε
            by_cases h0 : s ε = 0
            · simp [h0]
            · field_simp
              ring_nf
              rw [Complex.I_sq]; ring
          rw [heq2]
          have := (hs.const_mul ((π:ℂ))).mul_const ((x:ℂ) ^ 2)
          simpa using this
        have hc := (Complex.continuous_exp.tendsto 0).comp hlim0
        simpa using hc
      · simp only [if_neg hn]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        -- ‖T_n‖ = exp(A ε) with A ε → -∞
        have hAtend : Filter.Tendsto
            (fun ε => -π * (n:ℝ) ^ 2 * ((s ε).re / Complex.normSq (s ε)) + π * x ^ 2 * (s ε).re)
            l Filter.atBot := by
          have hne : (n:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
          have hpos : (0:ℝ) < π * (n:ℝ) ^ 2 := by positivity
          have hfirst : Filter.Tendsto
              (fun ε => -(π * (n:ℝ) ^ 2) * ((s ε).re / Complex.normSq (s ε))) l Filter.atBot :=
            Filter.Tendsto.const_mul_atTop_of_neg (by linarith) hdom
          have hsecond : Filter.Tendsto (fun ε => (π * x ^ 2) * (s ε).re) l (nhds 0) := by
            have := hre0.const_mul (π * x ^ 2); simpa using this
          refine (hfirst.atBot_add hsecond).congr (fun ε => ?_)
          ring
        refine Filter.Tendsto.congr' ?_ (Real.tendsto_exp_atBot.comp hAtend)
        filter_upwards [hre] with ε hε
        rw [Function.comp_apply, hnorm n ε hε]
    · -- domination
      have hsre1 : ∀ᶠ ε in l, (s ε).re ≤ 1 :=
        hre0.eventually (eventually_le_nhds (by norm_num))
      filter_upwards [hre, hdom.eventually_ge_atTop 1, hsre1] with ε hε hdomε hsre n
      rw [hnorm n ε hε]
      have hb : Real.exp (π * x ^ 2) * Real.exp (-π * n ^ 2)
          = Real.exp (π * x ^ 2 + -π * n ^ 2) := (Real.exp_add _ _).symm
      rw [hb, Real.exp_le_exp]
      have hpi : (0:ℝ) < π := Real.pi_pos
      have hn2 : (0:ℝ) ≤ (n:ℝ) ^ 2 := sq_nonneg _
      have hx2 : (0:ℝ) ≤ x ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hpi.le hn2) (by linarith : (0:ℝ) ≤ (s ε).re / Complex.normSq (s ε) - 1),
        mul_nonneg (mul_nonneg hpi.le hx2) (by linarith : (0:ℝ) ≤ 1 - (s ε).re)]
  have := h1.mul h2
  simpa using this

/-- Poisson dual of `Gtheta`: with `b = ε - 2i/N` (so `Re b = ε > 0`),
`Gtheta N ε = b^{-1/2} · ∑ₙ exp(-π n²/b)`. -/
lemma Gtheta_poisson (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Gtheta N ε = 1 / ((ε:ℂ) - 2 * I / N) ^ (1/2 : ℂ) *
      ∑' n : ℤ, Complex.exp (-(π:ℂ) / ((ε:ℂ) - 2 * I / N) * n ^ 2) := by
  have hre : 0 < ((ε:ℂ) - 2 * I / N).re := by
    have : ((ε:ℂ) - 2 * I / N).re = ε := by
      simp [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]
    rw [this]; exact hε
  unfold Gtheta
  exact Complex.tsum_exp_neg_mul_int_sq hre

/-- Norm of the dual term. -/
lemma dual_term_norm2 (b : ℂ) (n : ℤ) :
    ‖Complex.exp (-(π:ℂ) / b * n ^ 2)‖ = Real.exp (-(π * (b.re / Complex.normSq b)) * (n:ℝ) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  have h : -(π:ℂ) / b * (n:ℂ) ^ 2 = (((-(π * (n:ℝ) ^ 2)) : ℝ) : ℂ) * b⁻¹ := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.inv_re]
  ring

/-- Dual decomposition (mod-2 regrouping with phase extraction).  With `b = ε - 2i/N`
and `s = 4/b - 2iN`, the dual theta splits as a sum over `j ∈ {0,1}`. -/
theorem dual_decomp (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (∑' n : ℤ, Complex.exp (-(π:ℂ) / ((ε:ℂ) - 2 * I / N) * n ^ 2)) =
      ∑ j ∈ Finset.range 2, Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
        ∑' m : ℤ, Complex.exp (-(π:ℂ) * (4 / ((ε:ℂ) - 2 * I / N) - 2 * I * N) * (m + (j:ℝ) / 2) ^ 2) := by
  set b : ℂ := (ε:ℂ) - 2 * I / N with hb
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbre : b.re = ε := by
    simp [hb, Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]
  have hbne : b ≠ 0 := by
    intro h; rw [h] at hbre; simp at hbre; exact hε.ne' hbre.symm
  set s : ℂ := 4 / b - 2 * I * N with hs
  set F : ℤ → ℂ := fun n => Complex.exp (-(π:ℂ) / b * n ^ 2) with hF
  have hsum : Summable F := by
    rw [← summable_norm_iff]
    have hc : 0 < π * (b.re / Complex.normSq b) := by
      apply mul_pos Real.pi_pos
      apply div_pos
      · rw [hbre]; exact hε
      · exact Complex.normSq_pos.mpr hbne
    apply (summable_exp_neg_mul_sq hc).congr
    intro n; rw [hF, dual_term_norm2 b n]
  have hsum2 : Summable (fun p : ℤ × Fin 2 => F ((Int.divModEquiv 2).symm p)) :=
    hsum.comp_injective (Int.divModEquiv 2).symm.injective
  have hterm : ∀ (q : ℤ) (r : Fin 2),
      F ((Int.divModEquiv 2).symm (q, r)) =
        Complex.exp (-(π:ℂ) * I * N * (r:ℕ) ^ 2 / 2) *
          Complex.exp (-(π:ℂ) * s * ((q:ℂ) + ((r:ℕ):ℝ) / 2) ^ 2) := by
    intro q r
    have key : -(π:ℂ) / b * (((Int.divModEquiv 2).symm (q, r) : ℤ) : ℂ) ^ 2
        = (-(π:ℂ) * I * N * (r:ℕ) ^ 2 / 2 + -(π:ℂ) * s * ((q:ℂ) + ((r:ℕ):ℝ) / 2) ^ 2)
          + ((-(N:ℤ) * (q ^ 2 + q * (r:ℕ)) : ℤ) : ℂ) * (2 * π * I) := by
      have hsymm : ((Int.divModEquiv 2).symm (q, r) : ℤ) = q * 2 + (r:ℕ) := rfl
      rw [hsymm, hs]; push_cast; field_simp; ring
    rw [hF]
    show Complex.exp (-(π:ℂ) / b * (((Int.divModEquiv 2).symm (q, r) : ℤ) : ℂ) ^ 2) = _
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add]
  rw [← (Int.divModEquiv 2).symm.tsum_eq F]
  rw [hsum2.tsum_prod' (fun q => (hasSum_fintype
        (fun r : Fin 2 => F ((Int.divModEquiv 2).symm (q, r)))).summable)]
  simp_rw [tsum_fintype]
  rw [Summable.tsum_finsetSum (fun r _ => ?_)]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
          ∑' m : ℤ, Complex.exp (-(π:ℂ) * s * ((m:ℂ) + (j:ℝ) / 2) ^ 2))]
    apply Finset.sum_congr rfl
    intro r _
    rw [← tsum_mul_left]
    refine tsum_congr (fun q => ?_)
    rw [hterm q r]
  · exact hsum2.comp_injective (fun a b h => by simpa using h)



lemma G_const (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (Real.sqrt ε : ℂ) * (((ε:ℂ) - 2 * I / N) ^ (1/2 : ℂ))⁻¹ *
        (((4 / ((ε:ℂ) - 2 * I / N) - 2 * I * N)) ^ (1/2 : ℂ))⁻¹
      = ((-2 * I * N : ℂ)) ^ (-1/2 : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h2N : (-2 * I * N : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
    exact ⟨⟨by norm_num, I_ne_zero⟩, hNc⟩
  have hbX : (ε:ℂ) - 2 * I / N ≠ 0 := by
    intro h
    have : ((ε:ℂ) - 2 * I / N).re = ε := by
      simp [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]
    rw [h] at this; simp at this; exact hε.ne' this.symm
  set b : ℂ := (ε:ℂ) - 2 * I / N with hb
  set s : ℂ := 4 / b - 2 * I * N with hs
  have hbinv : b * (4 / b) = 4 := by rw [mul_comm]; exact div_mul_cancel₀ 4 hbX
  have hbs : b * s = (ε:ℂ) * (-2 * I * N) := by
    rw [hs, mul_sub, hbinv, hb]; field_simp; linear_combination (4:ℂ) * Complex.I_sq
  have hsne : s ≠ 0 := by
    intro h; rw [h, mul_zero] at hbs
    rcases mul_eq_zero.mp hbs.symm with h1 | h1
    · exact hεc h1
    · exact h2N h1
  have h1s : s⁻¹ = (((((N:ℝ) ^ 2 * ε)⁻¹) : ℝ) : ℂ) + (((((2 * N : ℝ))⁻¹) : ℝ) : ℂ) * I := by
    have hseq : s = (ε:ℂ) * (-2 * I * N) / b := by
      rw [eq_div_iff hbX, mul_comm]; exact hbs
    rw [hseq, inv_div, hb]; push_cast; field_simp; ring_nf; simp only [Complex.I_sq]; ring
  have hsre : 0 < s.re := by
    have hre : (0:ℝ) < s⁻¹.re := by
      rw [h1s, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero,
        Complex.ofReal_re]
      exact inv_pos.mpr (mul_pos (pow_pos hNr 2) hε)
    rw [Complex.inv_re] at hre
    rcases div_pos_iff.mp hre with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h (not_lt.mpr (Complex.normSq_nonneg s))
  have hargb : |arg b| < π / 2 := by
    rw [hb]; refine Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
    simp [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]; exact hε
  have hargs : |arg s| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hsre)
  have hargsum : arg b + arg s ∈ Set.Ioc (-π) π := by
    rw [abs_lt] at hargb hargs
    exact ⟨by nlinarith [hargb.1, hargs.1], by nlinarith [hargb.2, hargs.2, Real.pi_pos]⟩
  have hsqrt : (Real.sqrt ε : ℂ) = ((ε:ℂ)) ^ (1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hε.le]; norm_num
  rw [hsqrt, ← Complex.cpow_neg, ← Complex.cpow_neg]
  rw [Complex.cpow_def_of_ne_zero hεc, Complex.cpow_def_of_ne_zero hbX,
      Complex.cpow_def_of_ne_zero hsne, Complex.cpow_def_of_ne_zero h2N,
      ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hlogmul : Complex.log b + Complex.log s = Complex.log ((ε:ℂ) * (-2 * I * N)) := by
    rw [← hbs]; exact (Complex.log_mul hbX hsne hargsum).symm
  rw [Complex.log_ofReal_mul hε h2N, Complex.ofReal_log hε.le] at hlogmul
  linear_combination (-1/2 : ℂ) * hlogmul



lemma neg2IN_cpow (N : ℕ) (hN : 0 < N) :
    (-2 * I * (N:ℂ)) ^ (-1/2 : ℂ) = (1 + I) / (2 * (Real.sqrt N : ℂ)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have h2N : (-2 * I * (N:ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
    refine ⟨⟨by norm_num, I_ne_zero⟩, ?_⟩; exact_mod_cast hN.ne'
  have heq : (-2 * I * (N:ℂ)) = ((-2 * N : ℝ):ℂ) * I := by push_cast; ring
  have hnorm : ‖(-2 * I * (N:ℂ))‖ = 2 * N := by
    rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith)]
    ring
  have hre : (-2 * I * (N:ℂ)).re = 0 := by rw [heq]; simp
  have him : (-2 * I * (N:ℂ)).im < 0 := by rw [heq]; simp; nlinarith
  have harg : Complex.arg (-2 * I * (N:ℂ)) = -(π/2) := by
    rw [Complex.arg_eq_neg_pi_div_two_iff]; exact ⟨hre, him⟩
  rw [Complex.cpow_def_of_ne_zero h2N, Complex.log, hnorm, harg]
  have h2Npos : (0:ℝ) < 2 * N := by nlinarith
  have hsqrtN : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hexp : ((Real.log (2 * N) : ℂ) + (((-(π/2)):ℝ) : ℂ) * I) * (-1/2 : ℂ)
      = ((-(Real.log (2 * N) / 2) : ℝ) : ℂ) + ((π/4 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hA : Real.exp (-(Real.log (2 * (N:ℝ)) / 2)) = 1 / Real.sqrt (2 * N) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2Npos, one_div, ← Real.exp_neg]
    congr 1; ring
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsN : Real.sqrt (N:ℝ) ≠ 0 := hsqrtN.ne'
  have hscalar : (1/Real.sqrt (2*(N:ℝ))) * (Real.sqrt 2 / 2) = 1/(2*Real.sqrt N) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2) N]
    field_simp
  rw [hA]
  have e1 : (↑(1/Real.sqrt (2*(N:ℝ))) : ℂ) * (↑(Real.sqrt 2/2) + ↑(Real.sqrt 2/2) * I)
      = ↑((1/Real.sqrt (2*(N:ℝ)))*(Real.sqrt 2/2)) * (1 + I) := by push_cast; ring
  rw [e1, hscalar]; push_cast; ring
noncomputable def sfun (N : ℕ) (ε : ℝ) : ℂ := 4 / ((ε:ℂ) - 2 * I / N) - 2 * I * N

-- basic facts
lemma bX_ne (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) : (ε:ℂ) - 2 * I / N ≠ 0 := by
  intro h
  have : ((ε:ℂ) - 2 * I / N).re = ε := by
    simp [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [h] at this; simp at this; exact hε.ne' this.symm

lemma sfun_ne (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) : sfun N ε ≠ 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h2N : (-2 * I * N : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
    exact ⟨⟨by norm_num, I_ne_zero⟩, hNc⟩
  have hbX := bX_ne N hN ε hε
  have hbinv : ((ε:ℂ) - 2 * I / N) * (4 / ((ε:ℂ) - 2 * I / N)) = 4 := by
    rw [mul_comm]; exact div_mul_cancel₀ 4 hbX
  have hbs : ((ε:ℂ) - 2 * I / N) * sfun N ε = (ε:ℂ) * (-2 * I * N) := by
    rw [sfun, mul_sub, hbinv]; field_simp; linear_combination (4:ℂ) * Complex.I_sq
  intro h
  rw [h, mul_zero] at hbs
  rcases mul_eq_zero.mp hbs.symm with h1 | h1
  · exact hεc h1
  · exact h2N h1

lemma scpow_ne (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) : (sfun N ε) ^ (1/2 : ℂ) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (sfun_ne N hN ε hε)]
  exact Complex.exp_ne_zero _

lemma H_decomp (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (Real.sqrt ε : ℂ) * Gtheta N ε =
      ∑ j ∈ Finset.range 2, Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
        ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)) *
        ((sfun N ε) ^ (1/2 : ℂ) *
          ∑' m : ℤ, Complex.exp (-(π:ℂ) * (sfun N ε) * ((m:ℂ) + (j:ℝ) / 2) ^ 2)) := by
  rw [Gtheta_poisson N ε hε, dual_decomp N hN ε hε]
  rw [mul_sum, mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  set b : ℂ := (ε:ℂ) - 2 * I / N with hb
  set s : ℂ := 4 / b - 2 * I * N with hs
  have hsfun : sfun N ε = s := by rw [sfun, hs, hb]
  rw [hsfun]
  have hsne : (s ^ (1/2 : ℂ)) ≠ 0 := by rw [← hsfun]; exact scpow_ne N hN ε hε
  have hGc := G_const N hN ε hε
  rw [← hb, ← hs] at hGc
  set E : ℂ := Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) with hE
  set V : ℂ := ∑' m : ℤ, Complex.exp (-(π:ℂ) * s * ((m:ℂ) + (j:ℝ) / 2) ^ 2) with hV
  have hcancel : (s ^ (1/2 : ℂ))⁻¹ * s ^ (1/2 : ℂ) = 1 := inv_mul_cancel₀ hsne
  calc (Real.sqrt ε : ℂ) * (1 / b ^ (1/2 : ℂ) * (E * V))
      = E * V * ((Real.sqrt ε : ℂ) * (b ^ (1/2 : ℂ))⁻¹) := by rw [one_div]; ring
    _ = E * V * ((Real.sqrt ε : ℂ) * (b ^ (1/2 : ℂ))⁻¹) * ((s ^ (1/2 : ℂ))⁻¹ * s ^ (1/2 : ℂ)) := by
          rw [hcancel]; ring
    _ = E * ((Real.sqrt ε : ℂ) * (b ^ (1/2 : ℂ))⁻¹ * (s ^ (1/2 : ℂ))⁻¹) * (s ^ (1/2 : ℂ) * V) := by ring
    _ = E * (-2 * I * N : ℂ) ^ (-1/2 : ℂ) * (s ^ (1/2 : ℂ) * V) := by rw [hGc]

lemma sfun_formula (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    sfun N ε = (ε:ℂ) * (-2 * I * N) / ((ε:ℂ) - 2 * I / N) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbX := bX_ne N hN ε hε
  have hbinv : ((ε:ℂ) - 2 * I / N) * (4 / ((ε:ℂ) - 2 * I / N)) = 4 := by
    rw [mul_comm]; exact div_mul_cancel₀ 4 hbX
  have hbs : ((ε:ℂ) - 2 * I / N) * sfun N ε = (ε:ℂ) * (-2 * I * N) := by
    rw [sfun, mul_sub, hbinv]; field_simp; linear_combination (4:ℂ) * Complex.I_sq
  rw [eq_div_iff hbX, mul_comm]; exact hbs

lemma sfun_inv (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (sfun N ε)⁻¹ = (((((N:ℝ) ^ 2 * ε)⁻¹) : ℝ) : ℂ) + (((((2 * N : ℝ))⁻¹) : ℝ) : ℂ) * I := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hεc : (ε:ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  rw [sfun_formula N hN ε hε, inv_div]
  rw [div_eq_iff (by simp [hεc, hNc, I_ne_zero])]
  push_cast
  field_simp
  linear_combination ((ε:ℂ)*(N:ℂ)) * Complex.I_sq

lemma sfun_re_pos (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) : 0 < (sfun N ε).re := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hre : (0:ℝ) < (sfun N ε)⁻¹.re := by
    rw [sfun_inv N hN ε hε, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero, Complex.ofReal_re]
    exact inv_pos.mpr (mul_pos (pow_pos hNr 2) hε)
  rw [Complex.inv_re] at hre
  rcases div_pos_iff.mp hre with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · exact absurd h (not_lt.mpr (Complex.normSq_nonneg _))

lemma sfun_redivnsq (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (sfun N ε).re / Complex.normSq (sfun N ε) = ((N:ℝ) ^ 2 * ε)⁻¹ := by
  have h := Complex.inv_re (sfun N ε)
  rw [sfun_inv N hN ε hε] at h
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero,
    Complex.ofReal_re] at h
  exact h.symm

lemma sfun_tendsto (N : ℕ) (hN : 0 < N) :
    Tendsto (sfun N) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hden0 : ((0:ℝ):ℂ) - 2 * I / N ≠ 0 := by
    simp only [Complex.ofReal_zero, zero_sub, neg_ne_zero]
    rw [div_ne_zero_iff]
    exact ⟨by simp [I_ne_zero], hNc⟩
  have hcont : ContinuousAt (fun x:ℝ => (x:ℂ) * (-2 * I * N) / ((x:ℂ) - 2 * I / N)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hden0
  have hval : (fun x:ℝ => (x:ℂ) * (-2 * I * N) / ((x:ℂ) - 2 * I / N)) 0 = 0 := by simp
  have ht : Tendsto (fun x:ℝ => (x:ℂ) * (-2 * I * N) / ((x:ℂ) - 2 * I / N)) (𝓝 0) (𝓝 0) := by
    have h := hcont.tendsto
    simpa only [Complex.ofReal_zero, zero_mul, zero_div] using h
  refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (sfun_formula N hN x hx).symm

lemma sfun_dom (N : ℕ) (hN : 0 < N) :
    Tendsto (fun ε => (sfun N ε).re / Complex.normSq (sfun N ε)) (𝓝[>] (0:ℝ)) atTop := by
  have h1 : Tendsto (fun ε:ℝ => ε⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun ε:ℝ => ((N:ℝ) ^ 2)⁻¹ * ε⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) h1
  refine (h2.congr (fun ε => by rw [← mul_inv])).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (sfun_redivnsq N hN ε hε).symm

lemma exp_neg_pi_I_half : Complex.exp (-(π:ℂ) * I / 2) = -I := by
  rw [show -(π:ℂ) * I / 2 = ((-(π/2):ℝ):ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.cos_pi_div_two,
    Real.sin_neg, Real.sin_pi_div_two]
  push_cast; ring

set_option maxHeartbeats 1000000 in
lemma gaussSumC_div (N : ℕ) (hN : 0 < N) :
    gaussSumC N / N = ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)) * (1 + (-I) ^ N) := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hre_ev : ∀ᶠ ε in 𝓝[>](0:ℝ), 0 < (sfun N ε).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε; exact sfun_re_pos N hN ε hε
  have hU : ∀ j : ℕ, Tendsto (fun ε => (sfun N ε) ^ (1/2:ℂ) *
      ∑' m : ℤ, Complex.exp (-(π:ℂ) * (sfun N ε) * ((m:ℂ) + (j:ℝ)/2) ^ 2)) (𝓝[>](0:ℝ)) (𝓝 1) := by
    intro j
    refine Filter.Tendsto.congr ?_ (complex_shifted_theta ((j:ℝ)/2) (𝓝[>](0:ℝ)) (sfun N)
      (sfun_tendsto N hN) hre_ev (sfun_dom N hN))
    intro ε
    congr 1
    exact tsum_congr (fun m => by congr 1; push_cast; ring)
  have hterm : ∀ j : ℕ, Tendsto (fun ε => Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
      ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)) * ((sfun N ε) ^ (1/2:ℂ) *
        ∑' m : ℤ, Complex.exp (-(π:ℂ) * (sfun N ε) * ((m:ℂ) + (j:ℝ)/2) ^ 2)))
      (𝓝[>](0:ℝ)) (𝓝 (Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) * ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)))) := by
    intro j
    have h := (hU j).const_mul (Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
      ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)))
    rwa [mul_one] at h
  have hsum : Tendsto (fun ε => (Real.sqrt ε:ℂ) * Gtheta N ε) (𝓝[>](0:ℝ))
      (𝓝 (∑ j ∈ Finset.range 2, Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) *
        ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)))) := by
    refine (tendsto_finset_sum (Finset.range 2) (fun j _ => hterm j)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (H_decomp N hN ε hε).symm
  have huniq : gaussSumC N / N = ∑ j ∈ Finset.range 2,
      Complex.exp (-(π:ℂ) * I * N * j ^ 2 / 2) * ((-2 * I * N : ℂ) ^ (-1/2 : ℂ)) :=
    tendsto_nhds_unique (sqrt_eps_Gtheta_limit N hN) hsum
  have hexpN : Complex.exp (-(π:ℂ) * I * N / 2) = (-I) ^ N := by
    rw [show -(π:ℂ) * I * N / 2 = (N:ℂ) * (-(π:ℂ) * I / 2) by ring, Complex.exp_nat_mul,
      exp_neg_pi_I_half]
  rw [huniq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.cast_zero, Nat.cast_one, one_pow, mul_one, zero_add]
  rw [show -(π:ℂ) * I * N * (0:ℂ) ^ 2 / 2 = 0 by ring, Complex.exp_zero, hexpN]
  ring

lemma gaussSumC_value (N : ℕ) (hN : 0 < N) :
    gaussSumC N = (Real.sqrt N : ℂ) * (1 + I) / 2 * (1 + (-I) ^ N) := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have huniq := gaussSumC_div N hN
  rw [neg2IN_cpow N hN, div_eq_iff hNc] at huniq
  have hNeq : (N:ℂ) = (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_cast
  rw [huniq, hNeq]
  field_simp
