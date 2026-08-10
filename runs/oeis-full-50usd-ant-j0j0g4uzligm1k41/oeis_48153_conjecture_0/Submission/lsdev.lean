import FormalConjectures.Util.ProblemImports

open Complex Real Filter Topology
open scoped BigOperators

theorem poisson_rewrite (c : ℕ) (r : ℤ) (t : ℝ) (ht : 0 < t) (hc : 0 < c) :
    (∑' m : ℤ, (Real.exp (-π * ((c:ℝ)*m + r)^2 * t) : ℂ)) =
      Complex.exp (-π * r^2 * t) * (1 / ((c:ℂ)^2 * t) ^ (1/2 : ℂ)) *
        ∑' m : ℤ, Complex.exp (-π / ((c:ℂ)^2 * t) * ((m:ℂ) + I * (-(c*r*t)))^2) := by
  have hcteq : ((c:ℂ)^2 * t) = (((c:ℝ)^2 * t : ℝ) : ℂ) := by push_cast; ring
  have ha : 0 < ((c:ℂ)^2 * t).re := by
    rw [hcteq, Complex.ofReal_re]; positivity
  have key := Complex.tsum_exp_neg_quadratic ha (-(c*r*t) : ℂ)
  rw [mul_assoc, ← key, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

-- Clean form: c*√t * (inner sum) = jacobiTheta₂ (r/c) (i/(c²t))
theorem inner_eq (c : ℕ) (r : ℤ) (t : ℝ) (ht : 0 < t) (hc : 0 < c) :
    ((c : ℂ) * (Real.sqrt t : ℝ)) * (∑' m : ℤ, (Real.exp (-π * ((c:ℝ)*m + r)^2 * t) : ℂ)) =
      jacobiTheta₂ ((r:ℂ)/(c:ℂ)) (I / ((c:ℂ)^2 * t)) := by
  rw [poisson_rewrite c r t ht hc]
  have hcpow : ((c:ℂ)^2 * t) ^ (1/2 : ℂ) = ((c:ℂ) * (Real.sqrt t : ℝ)) := by
    have h1 : ((c:ℂ)^2 * t) = (((c:ℝ)^2 * t : ℝ) : ℂ) := by push_cast; ring
    rw [h1, show (1/2:ℂ) = (((1:ℝ)/2 : ℝ):ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity)]
    rw [show ((c:ℂ) * (Real.sqrt t:ℝ)) = (((c:ℝ) * Real.sqrt t : ℝ):ℂ) by push_cast; ring]
    rw [Complex.ofReal_inj, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  have hne : ((c:ℂ) * (Real.sqrt t : ℝ)) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hc' : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr hc.ne'
    · exact_mod_cast this.ne'
  rw [hcpow]
  rw [show ((c:ℂ)*(Real.sqrt t:ℝ)) * (Complex.exp (-↑π * ↑r^2 * ↑t) * (1/((c:ℂ)*(Real.sqrt t:ℝ))) *
      (∑' m : ℤ, Complex.exp (-↑π / ((c:ℂ)^2 * ↑t) * ((m:ℂ) + I * (-(↑c*↑r*↑t)))^2)))
    = (((c:ℂ)*(Real.sqrt t:ℝ)) * (1/((c:ℂ)*(Real.sqrt t:ℝ)))) *
      (Complex.exp (-↑π * ↑r^2 * ↑t) *
      (∑' m : ℤ, Complex.exp (-↑π / ((c:ℂ)^2 * ↑t) * ((m:ℂ) + I * (-(↑c*↑r*↑t)))^2))) by ring]
  rw [mul_one_div_cancel hne, one_mul]
  unfold jacobiTheta₂ jacobiTheta₂_term
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [← Complex.exp_add]
  congr 1
  have hc0 : ((c:ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have ht0 : ((t:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [show ((m:ℂ) + Complex.I * (-(↑c*↑r*↑t)))^2
        = (m:ℂ)^2 - 2*Complex.I*(↑c*↑r*↑t)*m + (Complex.I^2)*(↑c*↑r*↑t)^2 by ring,
      Complex.I_sq]
  field_simp
  linear_combination (-(m:ℂ)^2) * Complex.I_sq

-- jacobiTheta₂ (r/c) (I/(c²t)) → 1 as t → 0⁺
theorem theta_limit (c : ℕ) (r : ℤ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => jacobiTheta₂ ((r:ℂ)/(c:ℂ)) (I / ((c:ℂ)^2 * (t:ℝ))))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hc0R : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
  -- summable bound
  have hsum : Summable (fun n : ℤ => Real.exp (-π * ((1/(c:ℝ)^2) * (n:ℝ)^2))) := by
    have := summable_pow_mul_jacobiTheta₂_term_bound (0:ℝ) (show (0:ℝ) < 1/(c:ℝ)^2 by positivity) 0
    simpa using this
  -- termwise limits
  have hab : ∀ n : ℤ, Tendsto
      (fun t : ℝ => jacobiTheta₂_term n ((r:ℂ)/(c:ℂ)) (I / ((c:ℂ)^2 * (t:ℝ))))
      (𝓝[>] (0:ℝ)) (𝓝 (if n = 0 then (1:ℂ) else 0)) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp only [if_pos rfl, jacobiTheta₂_term]
      simpa using tendsto_const_nhds
    · rw [if_neg hn, tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : ∀ t : ℝ, 0 < t →
          ‖jacobiTheta₂_term n ((r:ℂ)/(c:ℂ)) (I / ((c:ℂ)^2 * (t:ℝ)))‖
            = Real.exp (-π * (n:ℝ)^2 * (1/((c:ℝ)^2 * t))) := by
        intro t ht
        rw [norm_jacobiTheta₂_term]
        congr 1
        have hzim : ((r:ℂ)/(c:ℂ)).im = 0 := by
          rw [Complex.div_im]; simp
        have htim : (I / ((c:ℂ)^2 * (t:ℝ))).im = 1/((c:ℝ)^2 * t) := by
          have hw : ((c:ℂ)^2 * (t:ℝ)) = (((c:ℝ)^2 * t : ℝ):ℂ) := by push_cast; ring
          rw [hw, Complex.div_ofReal_im, Complex.I_im, one_div]
        rw [hzim, htim]; ring
      -- reduce to exp(-c n^2 / t) -> 0
      have heq : (fun t : ℝ => ‖jacobiTheta₂_term n ((r:ℂ)/(c:ℂ)) (I / ((c:ℂ)^2 * (t:ℝ)))‖)
          =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => Real.exp ((-(π * (n:ℝ)^2 / (c:ℝ)^2)) * t⁻¹)) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hnorm t ht]
        congr 1
        field_simp
      rw [tendsto_congr' heq]
      have hconst : (-(π * (n:ℝ)^2 / (c:ℝ)^2)) < 0 := by
        have : (0:ℝ) < (n:ℝ)^2 := by
          have : (n:ℝ) ≠ 0 := by exact_mod_cast hn
          positivity
        have : (0:ℝ) < π * (n:ℝ)^2 / (c:ℝ)^2 := by positivity
        linarith
      have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
      have hexp : Tendsto (fun t : ℝ => (-(π * (n:ℝ)^2 / (c:ℝ)^2)) * t⁻¹)
          (𝓝[>] (0:ℝ)) atBot := hinv.const_mul_atTop_of_neg hconst
      exact Real.tendsto_exp_atBot.comp hexp
  -- dominated bound
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ∀ n : ℤ,
      ‖jacobiTheta₂_term n ((r:ℂ)/(c:ℂ)) (I / ((c:ℂ)^2 * (t:ℝ)))‖
        ≤ Real.exp (-π * ((1/(c:ℝ)^2) * (n:ℝ)^2)) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t < 1 :=
      (isOpen_Iio.eventually_mem (show (0:ℝ) ∈ Set.Iio 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hmem] with t ht ht1
    intro n
    have htpos : 0 < t := ht
    rw [norm_jacobiTheta₂_term]
    have hzim : ((r:ℂ)/(c:ℂ)).im = 0 := by rw [Complex.div_im]; simp
    have htim : (I / ((c:ℂ)^2 * (t:ℝ))).im = 1/((c:ℝ)^2 * t) := by
      have hw : ((c:ℂ)^2 * (t:ℝ)) = (((c:ℝ)^2 * t : ℝ):ℂ) := by push_cast; ring
      rw [hw, Complex.div_ofReal_im, Complex.I_im, one_div]
    rw [hzim, htim]
    apply Real.exp_le_exp.mpr
    rw [mul_zero, sub_zero]
    -- -π n² (1/(c²t)) ≤ -π (1/c² n²)
    have hct : (0:ℝ) < (c:ℝ)^2 * t := by positivity
    have hle : (1:ℝ)/((c:ℝ)^2) ≤ 1/((c:ℝ)^2 * t) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith [ht1.le]
    nlinarith [sq_nonneg (n:ℝ), mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg (n:ℝ)), hle]
  -- assemble via Tannery
  have main := tendsto_tsum_of_dominated_convergence hsum hab hbound
  have hg1 : ∑' n : ℤ, (if n = 0 then (1:ℂ) else 0) = 1 := tsum_ite_eq 0 1
  rw [show (1:ℂ) = ∑' n : ℤ, (if n = 0 then (1:ℂ) else 0) from hg1.symm]
  exact main

-- Grouping: jacobiTheta at 2/c + it splits into residues mod c, giving the Gauss sum coefficients.

theorem grouping (c : ℕ) (t : ℝ) (ht : 0 < t) (hc : 0 < c) :
    jacobiTheta ((2:ℂ)/(c:ℂ) + I * (t:ℝ)) =
      ∑ r ∈ Finset.range c, Complex.exp (2*π*I*(r:ℂ)^2/(c:ℂ)) *
        (∑' m : ℤ, (Real.exp (-π * ((c:ℝ)*m + r)^2 * t) : ℂ)) := by
  haveI : NeZero c := ⟨hc.ne'⟩
  set τ : ℂ := (2:ℂ)/(c:ℂ) + I * (t:ℝ) with hτdef
  have hτimval : τ.im = t := by
    rw [hτdef]
    simp [Complex.add_im, Complex.div_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτim : 0 < τ.im := by rw [hτimval]; exact ht
  have hsummable : Summable (fun n : ℤ => Complex.exp (π * I * (n:ℂ)^2 * τ)) := by
    have hh := (summable_jacobiTheta₂_term_iff (0:ℂ) τ).mpr hτim
    refine hh.congr (fun n => ?_)
    simp [jacobiTheta₂_term]
  set e : Fin c × ℤ ≃ ℤ := (Equiv.prodComm (Fin c) ℤ).trans (Int.divModEquiv c).symm with he
  have hsummable2 : Summable (fun p : Fin c × ℤ =>
      Complex.exp (π * I * ((e p : ℤ):ℂ)^2 * τ)) :=
    hsummable.comp_injective e.injective
  have hreindex : jacobiTheta τ
      = ∑' p : Fin c × ℤ, Complex.exp (π * I * ((e p : ℤ):ℂ)^2 * τ) := by
    rw [jacobiTheta, ← Equiv.tsum_eq e (fun n : ℤ => Complex.exp (π * I * (n:ℂ)^2 * τ))]
  have hstep : jacobiTheta τ
      = ∑ r : Fin c, ∑' q : ℤ, Complex.exp (π * I * ((e (r,q) : ℤ):ℂ)^2 * τ) := by
    rw [hreindex, hsummable2.tsum_prod' (fun r => (hsummable.comp_injective
      (fun a b hh => (Prod.ext_iff.mp (e.injective hh)).2))), tsum_fintype]
  -- per-term identity
  have hterm : ∀ (r : Fin c) (q : ℤ),
      Complex.exp (π * I * ((e (r,q) : ℤ):ℂ)^2 * τ)
        = Complex.exp (2*π*I*((r:ℕ):ℂ)^2/(c:ℂ)) * (Real.exp (-π * ((c:ℝ)*q + (r:ℕ))^2 * t) : ℂ) := by
    intro r q
    have hev : ((e (r,q) : ℤ):ℂ) = (q:ℂ)*(c:ℂ) + ((r:ℕ):ℂ) := by
      rw [show (e (r,q) : ℤ) = q * (c:ℤ) + (r:ℕ) from rfl]; push_cast; ring
    rw [hev, hτdef, Complex.ofReal_exp, ← Complex.exp_add,
      show (π*I*((q:ℂ)*(c:ℂ)+((r:ℕ):ℂ))^2*(2/(c:ℂ)+I*(t:ℝ)))
        = (2*π*I*((r:ℕ):ℂ)^2/(c:ℂ) + (((-π*((c:ℝ)*q+(r:ℕ))^2*t : ℝ)):ℂ))
          + ((q:ℂ)^2*(c:ℂ)+2*(q:ℂ)*((r:ℕ):ℂ))*(2*π*I) by
        have hcne : (c:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
        push_cast
        field_simp
        linear_combination ((c:ℂ) * (t:ℂ) * ((q:ℂ)*(c:ℂ) + ((r:ℕ):ℂ))^2) * Complex.I_sq,
      Complex.exp_add,
      show ((q:ℂ)^2*(c:ℂ)+2*(q:ℂ)*((r:ℕ):ℂ))*(2*π*I)
        = (((q^2*(c:ℤ)+2*q*(r:ℕ) : ℤ)):ℂ)*(2*π*I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hstep]
  have hpr : ∀ r : Fin c, (∑' q : ℤ, Complex.exp (π * I * ((e (r,q) : ℤ):ℂ)^2 * τ))
      = Complex.exp (2*π*I*((r:ℕ):ℂ)^2/(c:ℂ)) *
        (∑' m : ℤ, (Real.exp (-π * ((c:ℝ)*m + (r:ℕ))^2 * t) : ℂ)) := by
    intro r
    simp_rw [hterm r]
    rw [tsum_mul_left]
  rw [Finset.sum_congr rfl (fun r _ => hpr r)]
  rw [Fin.sum_univ_eq_sum_range (fun i => Complex.exp (2*π*I*((i:ℕ):ℂ)^2/(c:ℂ)) *
      (∑' m : ℤ, (Real.exp (-π * ((c:ℝ)*m + (i:ℕ))^2 * t) : ℂ))) c]

-- Combined: c√t · θ(2/c+it) → g(c) := Σ_r e^{2πir²/c}  (one side of Landsberg-Schaar)
theorem gauss_limit (c : ℕ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => ((c:ℂ) * (Real.sqrt t : ℝ)) * jacobiTheta ((2:ℂ)/(c:ℂ) + I * (t:ℝ)))
      (𝓝[>] (0:ℝ)) (𝓝 (∑ r ∈ Finset.range c, Complex.exp (2*π*I*(r:ℂ)^2/(c:ℂ)))) := by
  have hfun : ∀ t : ℝ, 0 < t →
      ((c:ℂ) * (Real.sqrt t : ℝ)) * jacobiTheta ((2:ℂ)/(c:ℂ) + I * (t:ℝ))
        = ∑ r ∈ Finset.range c, Complex.exp (2*π*I*(r:ℂ)^2/(c:ℂ)) *
            (((c:ℂ) * (Real.sqrt t : ℝ)) * (∑' m : ℤ, (Real.exp (-π * ((c:ℝ)*m + r)^2 * t) : ℂ))) := by
    intro t ht
    rw [grouping c t ht hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [tendsto_congr' (by filter_upwards [self_mem_nhdsWithin] with t ht using hfun t ht)]
  have : (∑ r ∈ Finset.range c, Complex.exp (2*π*I*(r:ℂ)^2/(c:ℂ)))
      = ∑ r ∈ Finset.range c, Complex.exp (2*π*I*(r:ℂ)^2/(c:ℂ)) * 1 := by simp
  rw [this]
  apply tendsto_finset_sum
  intro r _
  apply Tendsto.const_mul
  have hcomb : Tendsto (fun t : ℝ => ((c:ℂ) * (Real.sqrt t : ℝ)) *
      (∑' m : ℤ, (Real.exp (-π * ((c:ℝ)*m + r)^2 * t) : ℂ))) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have heq : (fun t : ℝ => ((c:ℂ) * (Real.sqrt t : ℝ)) *
        (∑' m : ℤ, (Real.exp (-π * ((c:ℝ)*m + r)^2 * t) : ℂ)))
        =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => jacobiTheta₂ ((r:ℂ)/(c:ℂ)) (I / ((c:ℂ)^2 * (t:ℝ)))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact inner_eq c r t ht hc
    rw [tendsto_congr' heq]
    exact theta_limit c r hc
  exact hcomb
