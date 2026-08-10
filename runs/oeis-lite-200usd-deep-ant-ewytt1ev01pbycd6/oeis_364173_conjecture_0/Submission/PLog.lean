import Mathlib

open scoped Topology
open Filter
open scoped ENNReal NNReal
open FormalMultilinearSeries

namespace PLog

variable {p : ℕ} [hp : Fact p.Prime]

/-- The `p`-adic logarithm of `x : ℤ_[p]`, valued in `ℚ_[p]`,
defined by `log(1+x) = ∑ (-1)^n x^{n+1}/(n+1)`. -/
noncomputable def padicLog (x : ℤ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, (-1) ^ n * (x : ℚ_[p]) ^ (n + 1) / (n + 1)

/-- The `n`-th term of the logarithm series. -/
private noncomputable def logTerm (x : ℤ_[p]) (n : ℕ) : ℚ_[p] :=
  (-1) ^ n * (x : ℚ_[p]) ^ (n + 1) / (n + 1)

lemma padicLog_eq_tsum (x : ℤ_[p]) : padicLog x = ∑' n : ℕ, logTerm x n := rfl

/-- `padicLog 0 = 0`. -/
@[simp] theorem padicLog_zero : padicLog (0 : ℤ_[p]) = 0 := by
  rw [padicLog]
  convert tsum_zero with n
  simp [zero_pow (Nat.succ_ne_zero n)]

/-- Norm of the inverse of a natural number cast into `ℚ_[p]` is at most the number. -/
lemma norm_natCast_inv_le (m : ℕ) : ‖(m : ℚ_[p])‖⁻¹ ≤ (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm0 : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm.ne'
    have hnorm : ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
      rw [Padic.norm_eq_zpow_neg_valuation hm0, Padic.valuation_natCast]
    rw [hnorm]
    rw [zpow_neg, inv_inv, zpow_natCast]
    have hdvd : p ^ (padicValNat p m) ∣ m := pow_padicValNat_dvd
    have hle : p ^ (padicValNat p m) ≤ m := Nat.le_of_dvd hm hdvd
    exact_mod_cast hle

/-- Exact norm of the `n`-th term. -/
lemma norm_logTerm_eq (x : ℤ_[p]) (n : ℕ) :
    ‖logTerm x n‖ = ‖x‖ ^ (n + 1) * ‖((n : ℚ_[p]) + 1)‖⁻¹ := by
  unfold logTerm
  rw [norm_div, norm_mul, norm_pow, norm_pow]
  have h1 : ‖(-1 : ℚ_[p])‖ = 1 := by simp
  rw [h1, one_pow, one_mul]
  have h2 : ‖(x : ℚ_[p])‖ = ‖x‖ := (PadicInt.norm_def).symm
  rw [h2]
  ring

/-- Bound on the norm of the `n`-th term. -/
lemma norm_logTerm_le (x : ℤ_[p]) (n : ℕ) :
    ‖logTerm x n‖ ≤ ‖x‖ ^ (n + 1) * (n + 1) := by
  rw [norm_logTerm_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : ((n : ℚ_[p]) + 1) = ((n + 1 : ℕ) : ℚ_[p]) := by push_cast; ring
  rw [this]
  have := norm_natCast_inv_le (p := p) (n + 1)
  push_cast at this ⊢
  linarith [this]

/-- The majorant `(n+1) ‖x‖^{n+1}` tends to `0` when `‖x‖ < 1`. -/
lemma tendsto_majorant (x : ℤ_[p]) (hx : ‖x‖ < 1) :
    Tendsto (fun n : ℕ => ‖x‖ ^ (n + 1) * ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hr0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * ‖x‖ ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hx
  have h2 : Tendsto (fun n : ℕ => ‖x‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hx
  have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ‖x‖ ^ n) atTop (𝓝 0) := by
    have := h1.add h2
    simp only [add_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have h4 := h3.const_mul (‖x‖)
  simp only [mul_zero] at h4
  refine h4.congr (fun n => ?_)
  ring

/-- The logarithm series terms tend to `0`. -/
lemma tendsto_logTerm (x : ℤ_[p]) (hx : ‖x‖ < 1) :
    Tendsto (logTerm x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => norm_logTerm_le x n)
  simpa using tendsto_majorant x hx

/-- **Summability** of the logarithm series. -/
lemma summable_logTerm (x : ℤ_[p]) (hx : ‖x‖ < 1) : Summable (logTerm x) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  exact tendsto_logTerm x hx

section Odd

omit hp in
/-- For an odd prime `p` and `k ≥ 1`, we have `k + 1 < p ^ k`. -/
lemma succ_lt_pow (hp3 : 3 ≤ p) {k : ℕ} (hk : 1 ≤ k) : k + 1 < p ^ k := by
  induction k, hk using Nat.le_induction with
  | base => simpa using hp3
  | succ k hk ih =>
      have hpk : k + 1 < p ^ k := ih
      calc k + 1 + 1 = (k + 1) + 1 := rfl
        _ < p ^ k + p ^ k := by omega
        _ ≤ p ^ k * p := by nlinarith [Nat.one_le_two_pow (n := k), pow_pos (show 0 < p by omega) k]
        _ = p ^ (k + 1) := by rw [pow_succ]

omit hp in
/-- For an odd prime `p` and `k ≥ 1`, `padicValNat p (k+1) < k`. -/
lemma padicValNat_succ_lt (hp3 : 3 ≤ p) {k : ℕ} (hk : 1 ≤ k) :
    padicValNat p (k + 1) < k := by
  have hp1 : 1 < p := by omega
  have hdvd : p ^ (padicValNat p (k + 1)) ∣ (k + 1) := pow_padicValNat_dvd
  have hle : p ^ (padicValNat p (k + 1)) ≤ k + 1 := Nat.le_of_dvd (by omega) hdvd
  have hlt : p ^ (padicValNat p (k + 1)) < p ^ k :=
    lt_of_le_of_lt hle (succ_lt_pow hp3 hk)
  exact (Nat.pow_lt_pow_iff_right hp1).mp hlt

/-- `‖x‖ ≤ p⁻¹` whenever `‖x‖ < 1`. -/
lemma norm_le_inv (x : ℤ_[p]) (hx : ‖x‖ < 1) : ‖x‖ ≤ (p : ℝ)⁻¹ := by
  have h := (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one x (-1)).mpr (by simpa using hx)
  simpa using h

/-- Uniform bound on tail terms: for odd `p` and index `k ≥ 1`,
`‖logTerm x k‖ ≤ p⁻¹ ‖x‖`. -/
lemma norm_logTerm_tail_le (hp3 : 3 ≤ p) (x : ℤ_[p]) (hx : ‖x‖ < 1) (n : ℕ) :
    ‖logTerm x (n + 1)‖ ≤ (p : ℝ)⁻¹ * ‖x‖ := by
  set k := n + 1 with hkdef
  have hk : 1 ≤ k := by omega
  have hxinv : ‖x‖ ≤ (p : ℝ)⁻¹ := norm_le_inv x hx
  have hP0 : (0 : ℝ) < p := by
    have := hp.out.pos; exact_mod_cast this
  -- norm of the (k+1)-th natural number cast
  have hm0 : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hnormval : ‖((k : ℚ_[p]) + 1)‖⁻¹ = (p : ℝ) ^ (padicValNat p (k + 1)) := by
    have : ((k : ℚ_[p]) + 1) = ((k + 1 : ℕ) : ℚ_[p]) := by push_cast; ring
    rw [this, Padic.norm_eq_zpow_neg_valuation hm0, Padic.valuation_natCast,
      zpow_neg, inv_inv, zpow_natCast]
  rw [norm_logTerm_eq, hnormval]
  -- ‖x‖^(k+1) * p^v = ‖x‖ * (‖x‖^k * p^v)
  have hsplit : ‖x‖ ^ (k + 1) * (p : ℝ) ^ (padicValNat p (k + 1))
      = ‖x‖ * (‖x‖ ^ k * (p : ℝ) ^ (padicValNat p (k + 1))) := by ring
  rw [hsplit, mul_comm ((p : ℝ)⁻¹) ‖x‖]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  -- ‖x‖^k * p^v ≤ p⁻¹
  have hv : padicValNat p (k + 1) < k := padicValNat_succ_lt hp3 hk
  have hxk : ‖x‖ ^ k ≤ ((p : ℝ)⁻¹) ^ k := pow_le_pow_left₀ (norm_nonneg _) hxinv k
  have hstep : ‖x‖ ^ k * (p : ℝ) ^ (padicValNat p (k + 1))
      ≤ ((p : ℝ)⁻¹) ^ k * (p : ℝ) ^ (padicValNat p (k + 1)) := by
    apply mul_le_mul_of_nonneg_right hxk (by positivity)
  refine hstep.trans ?_
  rw [inv_pow, ← zpow_natCast (p : ℝ) k, ← zpow_natCast (p : ℝ) (padicValNat p (k + 1))]
  rw [← zpow_neg]
  rw [← zpow_add₀ (ne_of_gt hP0)]
  have hexp : (-(k : ℤ)) + (padicValNat p (k + 1) : ℤ) ≤ (-1 : ℤ) := by
    have : (padicValNat p (k + 1) : ℤ) < (k : ℤ) := by exact_mod_cast hv
    omega
  have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  calc (p : ℝ) ^ ((-(k : ℤ)) + (padicValNat p (k + 1) : ℤ))
      ≤ (p : ℝ) ^ (-1 : ℤ) := by
        apply zpow_le_zpow_right₀ hp1r hexp
    _ = (p : ℝ)⁻¹ := by rw [zpow_neg_one]

/-- The `0`-th term is exactly `x`. -/
lemma norm_logTerm_zero (x : ℤ_[p]) : ‖logTerm x 0‖ = ‖x‖ := by
  rw [norm_logTerm_eq]
  simp

/-- Every term has norm `≤ ‖x‖`. -/
lemma norm_logTerm_le_self (hp3 : 3 ≤ p) (x : ℤ_[p]) (hx : ‖x‖ < 1) (n : ℕ) :
    ‖logTerm x n‖ ≤ ‖x‖ := by
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by exact_mod_cast hp.out.pos)]; exact_mod_cast (by omega : 1 ≤ p)
  cases n with
  | zero => rw [norm_logTerm_zero]
  | succ m =>
      refine (norm_logTerm_tail_le hp3 x hx m).trans ?_
      calc (p : ℝ)⁻¹ * ‖x‖ ≤ 1 * ‖x‖ :=
            mul_le_mul_of_nonneg_right hpinv (norm_nonneg _)
        _ = ‖x‖ := one_mul _

/-- **Integrality**: `‖padicLog x‖ ≤ ‖x‖`. -/
theorem norm_padicLog_le (hp3 : 3 ≤ p) (x : ℤ_[p]) (hx : ‖x‖ < 1) :
    ‖padicLog x‖ ≤ ‖x‖ := by
  rw [padicLog_eq_tsum]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) (norm_logTerm_le_self hp3 x hx)

/-- **Norm equality**: for an odd prime, `‖padicLog x‖ = ‖x‖` when `0 < ‖x‖ < 1`. -/
theorem norm_padicLog_eq (hp3 : 3 ≤ p) (x : ℤ_[p]) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    ‖padicLog x‖ = ‖x‖ := by
  have hxpos : 0 < ‖x‖ := by
    rw [norm_pos_iff]; exact hx0
  have hsum := summable_logTerm x hx
  have hsplit : padicLog x = logTerm x 0 + ∑' n : ℕ, logTerm x (n + 1) := by
    rw [padicLog_eq_tsum, hsum.tsum_eq_zero_add]
  set tail : ℚ_[p] := ∑' n : ℕ, logTerm x (n + 1) with htail
  have hpinv : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by exact_mod_cast hp.out.pos)]; exact_mod_cast (by omega : 1 < p)
  have htail_le : ‖tail‖ ≤ (p : ℝ)⁻¹ * ‖x‖ := by
    rw [htail]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro n
    exact norm_logTerm_tail_le hp3 x hx n
  have htail_lt : ‖tail‖ < ‖x‖ := by
    refine htail_le.trans_lt ?_
    calc (p : ℝ)⁻¹ * ‖x‖ < 1 * ‖x‖ := by
          apply mul_lt_mul_of_pos_right hpinv hxpos
      _ = ‖x‖ := one_mul _
  have hne : ‖logTerm x 0‖ ≠ ‖tail‖ := by
    rw [norm_logTerm_zero]; exact ne_of_gt htail_lt
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_logTerm_zero]
  exact max_eq_left (le_of_lt htail_lt)

/-- **Congruence extraction**: if `u ≡ 1 (mod p)` and `‖padicLog (u-1)‖ ≤ p^{-V}`,
then `p^V ∣ (u - 1)`.  In other words, `v_p(u-1) = v_p(log u)`, so a bound on the
logarithm yields the same bound on `u - 1`. -/
theorem sub_one_dvd_of_padicLog (hp3 : 3 ≤ p) (u : ℤ_[p]) (hu : ‖u - 1‖ < 1) (V : ℕ)
    (hlog : ‖padicLog (u - 1)‖ ≤ (p : ℝ) ^ (-(V : ℤ))) :
    (p : ℤ_[p]) ^ V ∣ (u - 1) := by
  rcases eq_or_ne (u - 1) 0 with h0 | h0
  · rw [h0]; exact dvd_zero _
  · have heq : ‖padicLog (u - 1)‖ = ‖u - 1‖ := norm_padicLog_eq hp3 (u - 1) hu h0
    rw [heq] at hlog
    have hmem : (u - 1) ∈ (Ideal.span {(p : ℤ_[p]) ^ V} : Ideal ℤ_[p]) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow (u - 1) V).mp hlog
    exact Ideal.mem_span_singleton.mp hmem

end Odd

noncomputable def cc : ℕ → ℚ_[p] := fun n => if n = 0 then 0 else (-1) ^ (n - 1) / (n : ℚ_[p])

noncomputable def PP (p : ℕ) [Fact p.Prime] : FormalMultilinearSeries ℚ_[p] ℚ_[p] ℚ_[p] :=
  ofScalars ℚ_[p] cc

lemma norm_natCast_inv_le' (m : ℕ) : ‖(m : ℚ_[p])‖⁻¹ ≤ (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm0 : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm.ne'
    have hnorm : ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
      rw [Padic.norm_eq_zpow_neg_valuation hm0, Padic.valuation_natCast]
    rw [hnorm, zpow_neg, inv_inv, zpow_natCast]
    exact_mod_cast Nat.le_of_dvd hm pow_padicValNat_dvd

lemma norm_cc_le (n : ℕ) : ‖(cc n : ℚ_[p])‖ ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [cc]
  · have : cc n = (-1 : ℚ_[p]) ^ (n - 1) / (n : ℚ_[p]) := by
      simp [cc, hn.ne']
    rw [this, norm_div, norm_pow]
    simp only [norm_neg, norm_one, one_pow, one_div]
    exact norm_natCast_inv_le' n

lemma one_le_radius_cc : (1 : ℝ≥0∞) ≤ (PP p).radius := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hsummable : Summable (fun n : ℕ => (n : ℝ) * (r : ℝ) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hr1)
  refine hsummable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  rw [PP, ofScalars_norm]
  gcongr
  exact norm_cc_le n


noncomputable def Lfun (p : ℕ) [Fact p.Prime] : ℚ_[p] → ℚ_[p] := (PP p).sum

lemma radius_pos_cc : 0 < (PP p).radius := lt_of_lt_of_le one_pos one_le_radius_cc

lemma hasFPS_L : HasFPowerSeriesOnBall (Lfun p) (PP p) 0 (PP p).radius :=
  (PP p).hasFPowerSeriesOnBall radius_pos_cc

lemma hasFPS_fderiv :
    HasFPowerSeriesOnBall (fderiv ℚ_[p] (Lfun p)) (PP p).derivSeries 0 (PP p).radius :=
  hasFPS_L.fderiv


-- term formula pieces

lemma diag_eq (n : ℕ) (z : ℚ_[p]) :
    (PP p).derivSeries n (fun _ => z) z = (-1)^n * z ^ (n+1) := by
  rw [derivSeries_apply_diag]
  show (n+1 : ℕ) • ((PP p) (n+1) (fun _ => z)) = (-1)^n * z ^ (n+1)
  simp only [PP, ofScalars_apply_eq, smul_eq_mul, nsmul_eq_mul]
  have hcc : (cc (n+1) : ℚ_[p]) = (-1)^n / ((n:ℚ_[p])+1) := by
    simp only [cc, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    congr 2; push_cast; ring
  rw [hcc]
  have hne : ((n:ℚ_[p])+1) ≠ 0 := by
    have : ((n+1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast at this; exact this
  push_cast; field_simp

lemma term_ne (n : ℕ) (z : ℚ_[p]) (hz : z ≠ 0) :
    (PP p).derivSeries n (fun _ => z) 1 = (-1)^n * z ^ n := by
  have key : (PP p).derivSeries n (fun _ => z) (z • (1:ℚ_[p]))
      = z • ((PP p).derivSeries n (fun _ => z) 1) := ContinuousLinearMap.map_smul _ z 1
  have hlin : (PP p).derivSeries n (fun _ => z) z = z * ((PP p).derivSeries n (fun _ => z) 1) := by
    simpa using key
  have h1 := diag_eq n z
  rw [hlin] at h1
  have : z * ((PP p).derivSeries n (fun _ => z) 1) = z * ((-1)^n * z^n) := by rw [h1]; ring
  exact mul_left_cancel₀ hz this

lemma term_all (n : ℕ) (z : ℚ_[p]) :
    (PP p).derivSeries n (fun _ => z) 1 = (-1)^n * z ^ n := by
  have hcont1 : Continuous (fun z : ℚ_[p] => (PP p).derivSeries n (fun _ => z) 1) :=
    (ContinuousLinearMap.apply ℚ_[p] ℚ_[p] (1:ℚ_[p])).continuous.comp
      (((PP p).derivSeries n).coe_continuous.comp (continuous_pi fun _ => continuous_id))
  have hcont2 : Continuous (fun z : ℚ_[p] => (-1:ℚ_[p])^n * z ^ n) := by fun_prop
  have := Continuous.ext_on (dense_compl_singleton (0:ℚ_[p])) hcont1 hcont2
    (fun z hz => term_ne n z hz)
  exact congrFun this z

lemma hasDeriv_L (z : ℚ_[p]) (hz : ‖z‖ < 1) : HasDerivAt (Lfun p) ((1 + z)⁻¹) z := by
  have hmem : z ∈ EMetric.ball (0 : ℚ_[p]) (PP p).radius := by
    rw [EMetric.mem_ball, edist_zero_eq_enorm]
    have h1 : ‖z‖ₑ < 1 := by
      rw [← enorm_norm]
      simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg z)] using
        (ENNReal.ofReal_lt_one).2 hz
    exact lt_of_lt_of_le h1 one_le_radius_cc
  have hsum : HasSum (fun n => (PP p).derivSeries n (fun _ => z)) (fderiv ℚ_[p] (Lfun p) z) := by
    have := hasFPS_fderiv.hasSum hmem
    simpa using this
  have hsum1 : HasSum (fun n => (PP p).derivSeries n (fun _ => z) 1)
      (fderiv ℚ_[p] (Lfun p) z 1) := by
    have := hsum.mapL (ContinuousLinearMap.apply ℚ_[p] ℚ_[p] (1:ℚ_[p]))
    simpa [ContinuousLinearMap.apply_apply] using this
  have hgeom : HasSum (fun n => (-1:ℚ_[p])^n * z^n) ((1 + z)⁻¹) := by
    have hznorm : ‖(-z)‖ < 1 := by rwa [norm_neg]
    have hg := hasSum_geometric_of_norm_lt_one hznorm
    have heq : (1 - (-z))⁻¹ = (1 + z)⁻¹ := by congr 1; ring
    rw [heq] at hg
    convert hg using 2 with n
    rw [neg_pow]; ring
  have hval : fderiv ℚ_[p] (Lfun p) z 1 = (1 + z)⁻¹ := by
    have heqfun : (fun n => (PP p).derivSeries n (fun _ => z) 1)
        = (fun n => (-1:ℚ_[p])^n * z^n) := by funext n; exact term_all n z
    rw [heqfun] at hsum1
    exact hsum1.unique hgeom
  have hdiff : DifferentiableAt ℚ_[p] (Lfun p) z :=
    (hasFPS_L.differentiableOn).differentiableAt (EMetric.isOpen_ball.mem_nhds hmem)
  have hfderiv : HasFDerivAt (Lfun p) (fderiv ℚ_[p] (Lfun p) z) z := hdiff.hasFDerivAt
  have hd := hfderiv.hasDerivAt
  rwa [hval] at hd


lemma norm_one_add (y : ℚ_[p]) (hy : ‖y‖ < 1) : ‖(1 + y : ℚ_[p])‖ = 1 := by
  rw [add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simp; exact ne_of_lt hy)]
  simp [le_of_lt hy]

lemma Fderiv_zero (y : ℚ_[p]) (hy : ‖y‖ < 1) (t : ℚ_[p]) (ht : ‖t‖ < 1) :
    HasDerivAt (fun s => Lfun p ((1+y)*s + y) - Lfun p s - Lfun p y) 0 t := by
  have ha : ‖(1 + y : ℚ_[p])‖ = 1 := norm_one_add y hy
  set z0 := (1+y)*t + y with hz0
  have hz0lt : ‖z0‖ < 1 := by
    have h1 : ‖(1+y)*t‖ < 1 := by rw [norm_mul, ha, one_mul]; exact ht
    calc ‖z0‖ = ‖(1+y)*t + y‖ := rfl
      _ ≤ max ‖(1+y)*t‖ ‖y‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt h1 hy
  have haff : HasDerivAt (fun s => (1+y)*s + y) (1+y) t := by
    simpa using ((hasDerivAt_id t).const_mul (1+y)).add_const y
  have hInner : HasDerivAt (Lfun p) ((1 + z0)⁻¹) z0 := hasDeriv_L z0 hz0lt
  have hG : HasDerivAt (fun s => Lfun p ((1+y)*s + y)) ((1+z0)⁻¹ * (1+y)) t :=
    hInner.comp t haff
  have hLt : HasDerivAt (Lfun p) ((1 + t)⁻¹) t := hasDeriv_L t ht
  have hF := (hG.sub hLt).sub_const (Lfun p y)
  have hval : (1+z0)⁻¹ * (1+y) - (1+t)⁻¹ = 0 := by
    have hy0 : (1 + y : ℚ_[p]) ≠ 0 := by
      intro h; rw [h] at ha; simp at ha
    have ht0 : (1 + t : ℚ_[p]) ≠ 0 := by
      intro h
      have : ‖(1 + t : ℚ_[p])‖ = 1 := norm_one_add t ht
      rw [h] at this; simp at this
    have hz : (1 + z0) = (1+y)*(1+t) := by rw [hz0]; ring
    rw [hz]
    field_simp
    ring
  rwa [hval] at hF

lemma hasFPS_G (y : ℚ_[p]) (hy : ‖y‖ < 1) :
    ∃ Q : FormalMultilinearSeries ℚ_[p] ℚ_[p] ℚ_[p],
      HasFPowerSeriesOnBall (fun t => Lfun p ((1+y)*t + y)) Q 0 ((PP p).radius - ‖y‖ₑ) := by
  have ha : ‖(1 + y : ℚ_[p])‖ = 1 := by
    rw [add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simp; exact ne_of_lt hy)]
    simp [le_of_lt hy]
  have hynn : (‖y‖₊ : ℝ≥0∞) < (PP p).radius := by
    rw [← enorm_eq_nnnorm]
    have h1 : ‖y‖ₑ < 1 := by
      rw [← enorm_norm]
      simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg y)] using
        (ENNReal.ofReal_lt_one).2 hy
    exact lt_of_lt_of_le h1 one_le_radius_cc
  have h1 := hasFPS_L.changeOrigin (y := y) hynn
  have h2 := h1.comp_sub (-y)
  simp only [add_neg_cancel, zero_add, sub_neg_eq_add] at h2
  set u : ℚ_[p] →L[ℚ_[p]] ℚ_[p] := (1+y) • ContinuousLinearMap.id ℚ_[p] ℚ_[p] with hu
  have hu0 : u 0 = 0 := by simp [hu]
  have hunorm : ‖u‖ₑ = 1 := by
    rw [hu, enorm_eq_nnnorm]
    norm_cast
    rw [nnnorm_smul]
    have : ‖(1+y : ℚ_[p])‖₊ = 1 := by rw [← NNReal.coe_inj]; push_cast; simpa using ha
    simp [this]
  rw [← hu0] at h2
  have h3 := h2.compContinuousLinearMap (u := u)
  rw [hunorm, div_one] at h3
  have hfun : (fun z => Lfun p (z + y)) ∘ u = (fun t => Lfun p ((1+y)*t + y)) := by
    funext t; simp [hu, Function.comp, mul_comm]
  rw [hfun] at h3
  exact ⟨_, by rw [enorm_eq_nnnorm]; exact h3⟩

lemma Lfun_zero : Lfun p 0 = 0 := by
  show ofScalarsSum cc 0 = 0
  rw [ofScalarsSum_zero]; simp [cc]

lemma mul_core (hp3 : 3 ≤ p) (x y : ℚ_[p]) (hx : ‖x‖ ≤ (p:ℝ)⁻¹) (hy : ‖y‖ ≤ (p:ℝ)⁻¹) :
    Lfun p (x + y + x*y) = Lfun p x + Lfun p y := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hpinv : (p:ℝ)⁻¹ < 1 := by rw [inv_lt_one₀ (by linarith)]; exact hp1
  have hy1 : ‖y‖ < 1 := lt_of_le_of_lt hy hpinv
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx hpinv
  obtain ⟨Q, hG⟩ := hasFPS_G y hy1
  set r := (PP p).radius - ‖y‖ₑ with hr
  -- L and const power series, subtract
  have hylt : ‖y‖ₑ < 1 := by
    rw [← enorm_norm]
    simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg y)] using
      (ENNReal.ofReal_lt_one).2 hy1
  have hrpos : (0:ℝ≥0∞) < r := by
    rw [hr]
    have : (0:ℝ≥0∞) < 1 - ‖y‖ₑ := by rw [tsub_pos_iff_lt]; exact hylt
    exact lt_of_lt_of_le this (tsub_le_tsub_right one_le_radius_cc _)
  have hLmono : HasFPowerSeriesOnBall (Lfun p) (PP p) 0 r :=
    hasFPS_L.mono hrpos (hr ▸ tsub_le_self)
  -- const and F power series
  have hconst : HasFPowerSeriesOnBall (fun _ : ℚ_[p] => Lfun p y)
      (constFormalMultilinearSeries ℚ_[p] ℚ_[p] (Lfun p y)) 0 r :=
    hasFPowerSeriesOnBall_const.mono hrpos le_top
  set F : ℚ_[p] → ℚ_[p] := fun s => Lfun p ((1+y)*s + y) - Lfun p s - Lfun p y with hF_def
  set QF := (Q - PP p) - constFormalMultilinearSeries ℚ_[p] ℚ_[p] (Lfun p y) with hQF
  have hF : HasFPowerSeriesOnBall F QF 0 r := (hG.sub hLmono).sub hconst
  -- derivative eventually zero
  have hev : (fderiv ℚ_[p] F) =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℚ_[p]) one_pos] with t ht
    rw [Metric.mem_ball, dist_zero_right] at ht
    have hd : HasDerivAt F 0 t := Fderiv_zero y hy1 t ht
    simp only [Pi.zero_apply]
    simpa using hd.hasFDerivAt.fderiv
  have hderivseries : QF.derivSeries = 0 :=
    hF.fderiv.hasFPowerSeriesAt.eq_zero_of_eventually hev
  -- coefficients vanish
  have F0 : F 0 = 0 := by
    show Lfun p ((1+y)*0 + y) - Lfun p 0 - Lfun p y = 0
    rw [show (1+y)*(0:ℚ_[p]) + y = y by ring, Lfun_zero]
    ring
  have hcoeff : ∀ n, QF.coeff n = 0 := by
    intro n
    match n with
    | 0 =>
      show QF 0 (fun _ => 1) = 0
      rw [hF.coeff_zero (fun _ => 1), F0]
    | (m+1) =>
      have h1 := QF.derivSeries_coeff_one m
      rw [hderivseries] at h1
      have hL0 : (0 : FormalMultilinearSeries ℚ_[p] ℚ_[p] (ℚ_[p] →L[ℚ_[p]] ℚ_[p])).coeff m 1 = 0 := by
        simp [FormalMultilinearSeries.coeff]
      rw [hL0] at h1
      have hz : (0:ℚ_[p]) = ((m+1:ℕ):ℚ_[p]) * QF.coeff (m+1) := by
        rw [← nsmul_eq_mul]; exact h1
      have hne : ((m+1:ℕ):ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      rcases mul_eq_zero.mp hz.symm with h | h
      · exact absurd h hne
      · exact h
  -- x in ball
  have hxmem : x ∈ EMetric.ball (0:ℚ_[p]) r := by
    rw [EMetric.mem_ball, edist_zero_eq_enorm, hr, lt_tsub_iff_right]
    have hreal : ‖x‖ + ‖y‖ < 1 := by
      have h3 : (2:ℝ)/p < 1 := by
        rw [div_lt_one (by linarith)]
        have : (3:ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      have h2 : (p:ℝ)⁻¹ + (p:ℝ)⁻¹ = 2/p := by ring
      linarith [hx, hy]
    have hsumnn : ‖x‖₊ + ‖y‖₊ < 1 := by rw [← NNReal.coe_lt_coe]; push_cast; exact hreal
    have hlt1 : ‖x‖ₑ + ‖y‖ₑ < 1 := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_add, ← ENNReal.coe_one,
        ENNReal.coe_lt_coe]
      exact hsumnn
    exact lt_of_lt_of_le hlt1 one_le_radius_cc
  -- F x = 0
  have hFx : F x = 0 := by
    have hs := hF.hasSum hxmem
    have hterms : ∀ n, QF n (fun _ => x) = 0 := by
      intro n
      rw [apply_eq_pow_smul_coeff, hcoeff n, smul_zero]
    have hs0 : HasSum (fun _ : ℕ => (0:ℚ_[p])) (F (0 + x)) := by
      refine hs.congr_fun ?_
      intro n; exact (hterms n).symm
    have hz := hs0.unique hasSum_zero
    rw [zero_add] at hz
    exact hz
  -- rearrange
  have hFx2 : Lfun p ((1+y)*x + y) - Lfun p x - Lfun p y = 0 := hFx
  have hxy : (1+y)*x + y = x + y + x*y := by ring
  rw [hxy] at hFx2
  linear_combination hFx2


lemma cc_succ_smul (x : ℤ_[p]) (n : ℕ) :
    (cc (n+1) : ℚ_[p]) • (x : ℚ_[p]) ^ (n+1) = logTerm x n := by
  have hcc : (cc (n+1) : ℚ_[p]) = (-1)^n / ((n:ℚ_[p])+1) := by
    simp only [cc, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    congr 2; push_cast; ring
  rw [hcc, logTerm, smul_eq_mul]
  ring

lemma Lfun_apply (z : ℚ_[p]) : Lfun p z = ∑' n : ℕ, (cc n : ℚ_[p]) • z ^ n := by
  show ofScalarsSum (cc : ℕ → ℚ_[p]) z = ∑' n : ℕ, (cc n : ℚ_[p]) • z ^ n
  exact ofScalars_sum_eq (cc : ℕ → ℚ_[p]) z

lemma padicLog_eq_Lfun (x : ℤ_[p]) (hx : ‖x‖ < 1) : padicLog x = Lfun p (x : ℚ_[p]) := by
  rw [Lfun_apply]
  set g : ℕ → ℚ_[p] := fun n => (cc n : ℚ_[p]) • (x : ℚ_[p]) ^ n with hg
  have hgsucc : ∀ n, g (n+1) = logTerm x n := fun n => cc_succ_smul x n
  have hg0 : g 0 = 0 := by simp [hg, cc]
  have hsummable : Summable g := by
    rw [← summable_nat_add_iff 1]
    have : (fun n => g (n+1)) = logTerm x := funext hgsucc
    rw [this]; exact summable_logTerm x hx
  rw [hsummable.tsum_eq_zero_add, hg0, zero_add, padicLog_eq_tsum]
  exact tsum_congr fun n => (hgsucc n).symm

lemma padicLog_mul (hp3 : 3 ≤ p) (x y : ℤ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    padicLog (x + y + x * y) = padicLog x + padicLog y := by
  have hxy : ‖x + y + x * y‖ < 1 := by
    have h1 : ‖x * y‖ < 1 := by
      rw [norm_mul]
      calc ‖x‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one x) (norm_nonneg _)
        _ = ‖y‖ := one_mul _
        _ < 1 := hy
    calc ‖x + y + x * y‖ ≤ max ‖x + y‖ ‖x * y‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt (lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)) h1
  rw [padicLog_eq_Lfun _ hxy, padicLog_eq_Lfun _ hx, padicLog_eq_Lfun _ hy]
  push_cast
  have hnx : ‖(x : ℚ_[p])‖ ≤ (p:ℝ)⁻¹ := by
    rw [← PadicInt.norm_def]; exact norm_le_inv x hx
  have hny : ‖(y : ℚ_[p])‖ ≤ (p:ℝ)⁻¹ := by
    rw [← PadicInt.norm_def]; exact norm_le_inv y hy
  exact mul_core hp3 (x : ℚ_[p]) (y : ℚ_[p]) hnx hny

lemma norm_prod_one_add_sub_one_lt {ι : Type*} (s : Finset ι) (f : ι → ℤ_[p])
    (hf : ∀ i ∈ s, ‖f i‖ < 1) : ‖(∏ i ∈ s, (1 + f i)) - 1‖ < 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa : ‖f a‖ < 1 := hf a (Finset.mem_insert_self a s)
    have hih : ‖(∏ i ∈ s, (1 + f i)) - 1‖ < 1 :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    set P := ∏ i ∈ s, (1 + f i) with hP
    have hfaP : ‖(1 + f a) * (P - 1)‖ < 1 := by
      rw [norm_mul]
      calc ‖1 + f a‖ * ‖P - 1‖ ≤ 1 * ‖P - 1‖ :=
            mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
        _ = ‖P - 1‖ := one_mul _
        _ < 1 := hih
    calc ‖(1 + f a) * P - 1‖
        = ‖(1 + f a) * (P - 1) + f a‖ := by
          rw [show (1 + f a) * P - 1 = (1 + f a) * (P - 1) + f a from by ring]
      _ ≤ max ‖(1 + f a) * (P - 1)‖ ‖f a‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt hfaP hfa

theorem padicLog_prod {ι : Type*} (hp3 : 3 ≤ p) (s : Finset ι) (f : ι → ℤ_[p])
    (hf : ∀ i ∈ s, ‖f i‖ < 1) :
    padicLog ((∏ i ∈ s, (1 + f i)) - 1) = ∑ i ∈ s, padicLog (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : ‖f a‖ < 1 := hf a (Finset.mem_insert_self a s)
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hPnorm : ‖(∏ i ∈ s, (1 + f i)) - 1‖ < 1 :=
      norm_prod_one_add_sub_one_lt s f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    set P := ∏ i ∈ s, (1 + f i) with hP
    set u := P - 1 with hu
    have hPu : P = 1 + u := by rw [hu]; ring
    have hkey : (1 + f a) * P - 1 = f a + u + f a * u := by rw [hPu]; ring
    rw [hkey, padicLog_mul hp3 (f a) u hfa hPnorm, hih]

theorem padicLog_pow (hp3 : 3 ≤ p) (x : ℤ_[p]) (hx : ‖x‖ < 1) (k : ℕ) :
    padicLog ((1 + x) ^ k - 1) = k • padicLog x := by
  have h := padicLog_prod hp3 (Finset.range k) (fun _ => x) (fun i _ => hx)
  simpa [Finset.prod_const, Finset.sum_const, Finset.card_range] using h


/-!
### Axiom check

We confirm that the key results depend only on the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms padicLog
#print axioms summable_logTerm
#print axioms norm_padicLog_le
#print axioms norm_padicLog_eq
#print axioms sub_one_dvd_of_padicLog


#print axioms padicLog_mul
#print axioms padicLog_prod
#print axioms padicLog_pow
