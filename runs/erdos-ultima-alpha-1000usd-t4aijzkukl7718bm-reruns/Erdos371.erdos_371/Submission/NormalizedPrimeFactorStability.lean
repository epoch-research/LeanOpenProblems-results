import FormalConjecturesUtil

/-! Pointwise quantitative dilation stability of the normalized logarithm of
 the largest prime factor. No neighboring-value symmetry is asserted. -/

namespace Erdos371NormalizedPrimeFactorStability

open Filter
open scoped Topology

noncomputable def level (n : ℕ) : ℝ :=
  Real.log (Nat.maxPrimeFac n : ℝ) / Real.log (n : ℝ)

lemma primeFac_pos {n : ℕ} (hn : 0 < n) : 0 < Nat.maxPrimeFac n := by
  by_cases h : n = 1
  · simp [h]
  · exact (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).pos

lemma log_primeFac_bounds (n : ℕ) :
    0 ≤ Real.log (Nat.maxPrimeFac n : ℝ) ∧
      Real.log (Nat.maxPrimeFac n : ℝ) ≤ Real.log (n : ℝ) := by
  refine ⟨Real.log_natCast_nonneg _, ?_⟩
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_le_log (Nat.cast_pos.mpr (primeFac_pos (Nat.pos_of_ne_zero hn)))
      (Nat.cast_le.mpr Nat.maxPrimeFac_le)

lemma level_bounds (n : ℕ) : 0 ≤ level n ∧ level n ≤ 1 := by
  refine ⟨div_nonneg (log_primeFac_bounds n).1 (Real.log_natCast_nonneg n), ?_⟩
  by_cases hn : n ≤ 1
  · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hn <;> simp [level]
  · have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    exact (div_le_one hlog).mpr (log_primeFac_bounds n).2

lemma normalized_max_bound {A L x c : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hx : 0 ≤ x) (hxL : x ≤ L) (hc : c ≤ A) :
    |max c x / (A+L) - x/L| ≤ A/(A+L) := by
  have hd : 0 < A+L := by linarith
  apply abs_le.mpr
  constructor
  · apply (neg_le_sub_iff_le_add).mpr
    apply (div_le_iff₀ hL).mpr
    have hm : x ≤ max c x := le_max_right _ _
    have ha := mul_le_mul_of_nonneg_right hxL hA
    have he : (max c x / (A+L) + A/(A+L))*L =
        (max c x * L + A*L)/(A+L) := by ring
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hd).mpr
    have hm : max c x ≤ A+x := max_le (by linarith) (by linarith)
    have hax : 0 ≤ A*x := mul_nonneg hA hx
    have he : (A/(A+L) + x/L)*(A+L) = A + x + A*x/L := by
      field_simp
      ring
    rw [he]
    have hh : 0 ≤ A*x/L := div_nonneg hax hL.le
    linarith

lemma log_primeFac_mul {a n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    Real.log (Nat.maxPrimeFac (a*n) : ℝ) =
      max (Real.log (Nat.maxPrimeFac a : ℝ)) (Real.log (Nat.maxPrimeFac n : ℝ)) := by
  rw [Nat.maxPrimeFac_mul ha.ne' hn.ne']
  rcases le_total (Nat.maxPrimeFac a) (Nat.maxPrimeFac n) with h | h
  · rw [max_eq_right h, max_eq_right]
    exact Real.log_le_log (Nat.cast_pos.mpr (primeFac_pos ha)) (Nat.cast_le.mpr h)
  · rw [max_eq_left h, max_eq_left]
    exact Real.log_le_log (Nat.cast_pos.mpr (primeFac_pos hn)) (Nat.cast_le.mpr h)

/-- Uniform in the multiplier, without any smooth exceptional set. -/
theorem dilation_bound {a n : ℕ} (ha : 0 < a) (hn : 1 < n) :
    |level (a*n) - level n| ≤ Real.log (a : ℝ) / Real.log (a*n : ℕ) := by
  have hn0 : 0 < n := by omega
  have he : Real.log (a*n : ℕ) = Real.log (a : ℝ) + Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha.ne')
      (Nat.cast_ne_zero.mpr hn0.ne')]
  unfold level
  rw [he, log_primeFac_mul ha hn0]
  exact normalized_max_bound (Real.log_natCast_nonneg a)
    (Real.log_pos (Nat.one_lt_cast.mpr hn))
    (log_primeFac_bounds n).1 (log_primeFac_bounds n).2
    (log_primeFac_bounds a).2

lemma dilation_bound' {a n : ℕ} (ha : 0 < a) (hn : 1 < n) :
    |level (a*n) - level n| ≤ Real.log (a : ℝ) / Real.log (n : ℝ) := by
  have hn0 : 0 < n := by omega
  apply (dilation_bound ha hn).trans
  apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg a)
    (Real.log_pos (Nat.one_lt_cast.mpr hn))
  apply Real.log_le_log (Nat.cast_pos.mpr hn0)
  exact_mod_cast (show n ≤ a*n by nlinarith)

/-- Every multiplier with subpower logarithmic size gives pointwise vanishing
change, even if a different multiplier is chosen at every input. -/
theorem subpower_stability (a : ℕ → ℕ)
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hlog : Tendsto (fun n => Real.log (a n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => level (a n*n) - level n) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · filter_upwards [ha, eventually_gt_atTop 1] with n han hn
    exact dilation_bound' han hn

theorem fixed_stability {a : ℕ} (ha : 0 < a) :
    Tendsto (fun n => level (a*n) - level n) atTop (𝓝 0) := by
  apply subpower_stability (fun _ => a) (Eventually.of_forall (fun _ => ha))
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- A strict increase of the numerator's integer argument remains a strict
increase after normalizing by the logarithms of successive integers, provided
that the old numerator is strictly below the old denominator. -/
lemma normalized_log_lt {p q n : ℕ} (hp : 1 < p) (hpn : p < n) (hpq : p < q) :
    Real.log (p : ℝ) / Real.log (n : ℝ) <
      Real.log (q : ℝ) / Real.log (n+1 : ℕ) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn10 : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hln1 : 0 < Real.log (n+1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n+1))
  have hr : (n+1 : ℕ) / (n : ℝ) < (q : ℝ) / p := by
    apply (div_lt_div_iff₀ hn0 hp0).mpr
    exact_mod_cast (show (n+1)*p < q*n by nlinarith)
  have hstep := Real.log_lt_log (div_pos hn10 hn0) hr
  rw [Real.log_div hn10.ne' hn0.ne', Real.log_div hq0.ne' hp0.ne'] at hstep
  have hinc : 0 ≤ Real.log (n+1 : ℕ) - Real.log (n : ℝ) := by
    apply sub_nonneg.mpr
    exact Real.log_le_log hn0 (by exact_mod_cast Nat.le_succ n)
  have hpL : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hp0 (Nat.cast_le.mpr hpn.le)
  apply (div_lt_div_iff₀ hln hln1).mpr
  have hs := mul_lt_mul_of_pos_right hstep hln
  have ht := mul_le_mul_of_nonneg_right hpL hinc
  nlinarith

lemma ascent_primeFac_lt_self {n : ℕ} (hn : 3 ≤ n)
    (h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) : Nat.maxPrimeFac n < n := by
  have hle := Nat.maxPrimeFac_le (n := n)
  by_contra hh
  have he : Nat.maxPrimeFac n = n := by omega
  have he' : Nat.maxPrimeFac (n+1) = n+1 := by
    have hh := Nat.maxPrimeFac_le (n := n+1)
    omega
  have hp : n.Prime := he ▸ Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hq : (n+1).Prime := he' ▸ Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have hp' := hp.eq_two_or_odd
  have hq' := hq.eq_two_or_odd
  omega

/-- Beyond the three initial inputs, the bounded normalized sequence has
exactly the same ascents as the largest-prime-factor sequence itself. -/
theorem level_ascent_iff {n : ℕ} (hn : 3 ≤ n) :
    level n < level (n+1) ↔ Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by
  constructor
  · intro h
    by_contra hh
    have hq : Nat.maxPrimeFac (n+1) ≤ Nat.maxPrimeFac n := by omega
    have hln : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hln1 : Real.log (n : ℝ) ≤ Real.log (n+1 : ℕ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast Nat.le_succ n)
    have he : level (n+1) ≤ level n := by
      unfold level
      calc
        _ ≤ Real.log (Nat.maxPrimeFac n : ℝ) / Real.log (n+1 : ℕ) :=
          div_le_div_of_nonneg_right
            (Real.log_le_log (Nat.cast_pos.mpr (primeFac_pos (by omega)))
              (Nat.cast_le.mpr hq)) (Real.log_natCast_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left (Real.log_natCast_nonneg _) hln hln1
    exact (not_lt.mpr he) h
  · intro h
    exact normalized_log_lt (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).one_lt
      (ascent_primeFac_lt_self hn h) h

end Erdos371NormalizedPrimeFactorStability

#print axioms Erdos371NormalizedPrimeFactorStability.dilation_bound
#print axioms Erdos371NormalizedPrimeFactorStability.subpower_stability

#print axioms Erdos371NormalizedPrimeFactorStability.level_ascent_iff
