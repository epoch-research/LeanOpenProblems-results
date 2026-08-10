import FormalConjectures.Util.ProblemImports

open scoped Real

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

section  -- ===== PLog =====

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




end PLog
end

section  -- ===== PKaz =====

/-!
# Balanced p-adic supercongruence

We prove a balanced supercongruence for products of "p-free factorials"
`W(m) = ∏_{1 ≤ j ≤ m, p ∤ j} j`, using the p-adic logarithm developed in
`Submission.PLog`.
-/

open PLog Finset

namespace PKaz

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Divisibility ↔ norm bridge, and reduction mod p -/

/-- `(p:ℤ_[p])^n ∣ x` is equivalent to `‖x‖ ≤ p^(-n)`. -/
lemma dvd_iff_norm_le (x : ℤ_[p]) (n : ℕ) :
    (p : ℤ_[p]) ^ n ∣ x ↔ ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

lemma dvd_of_toZModPow_zero {x : ℤ_[p]} {n : ℕ}
    (h : PadicInt.toZModPow n x = 0) : (p : ℤ_[p]) ^ n ∣ x := by
  have hmem : x ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) := h
  rw [PadicInt.ker_toZModPow] at hmem
  exact Ideal.mem_span_singleton.mp hmem

lemma dvd_of_toZMod_zero {x : ℤ_[p]} (h : PadicInt.toZMod x = 0) :
    (p : ℤ_[p]) ∣ x := by
  have hmem : x ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := h
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at hmem
  exact Ideal.mem_span_singleton.mp hmem

/-! ## p-adic inverses and harmonic sums -/

/-- p-adic inverse of a natural number, as an element of `ℤ_[p]`. -/
noncomputable def iv (i : ℕ) : ℤ_[p] := PadicInt.inv (i : ℤ_[p])

lemma norm_cast_eq_one {i : ℕ} (h : ¬ p ∣ i) : ‖(i : ℤ_[p])‖ = 1 := by
  rw [PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr h

lemma iv_mul_cancel {i : ℕ} (h : ¬ p ∣ i) : iv i * (i : ℤ_[p]) = 1 :=
  PadicInt.inv_mul (norm_cast_eq_one h)

lemma mul_iv_cancel {i : ℕ} (h : ¬ p ∣ i) : (i : ℤ_[p]) * iv i = 1 :=
  PadicInt.mul_inv (norm_cast_eq_one h)

lemma norm_iv {i : ℕ} (h : ¬ p ∣ i) : ‖(iv i : ℤ_[p])‖ = 1 := by
  exact PadicInt.isUnit_iff.mp (IsUnit.of_mul_eq_one (i : ℤ_[p]) (iv_mul_cancel h))

/-- The coercion of a p-adic inverse to `ℚ_[p]` is the field inverse. -/
lemma coe_iv {i : ℕ} (h : ¬ p ∣ i) : ((iv i : ℤ_[p]) : ℚ_[p]) = ((i : ℚ_[p]))⁻¹ := by
  have hne : ((i : ℚ_[p])) ≠ 0 := by
    have : ‖(i : ℤ_[p])‖ = 1 := norm_cast_eq_one h
    intro hc
    have : ‖(i : ℤ_[p])‖ = 0 := by
      rw [PadicInt.norm_def]; simpa using congrArg (fun z : ℚ_[p] => ‖z‖) hc
    rw [norm_cast_eq_one h] at this; exact one_ne_zero this
  have h1 : ((iv i : ℤ_[p]) : ℚ_[p]) * (i : ℚ_[p]) = 1 := by
    have h2 := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (iv_mul_cancel h)
    push_cast at h2
    simpa using h2
  calc ((iv i : ℤ_[p]) : ℚ_[p])
      = ((iv i : ℤ_[p]) : ℚ_[p]) * ((i : ℚ_[p]) * (i : ℚ_[p])⁻¹) := by
        rw [mul_inv_cancel₀ hne, mul_one]
    _ = (((iv i : ℤ_[p]) : ℚ_[p]) * (i : ℚ_[p])) * (i : ℚ_[p])⁻¹ := by ring
    _ = (i : ℚ_[p])⁻¹ := by rw [h1, one_mul]

/-- Reindex a sum over `Icc 1 (p-1)` (via `ℕ → ZMod p`) as a sum over the nonzero
elements of `ZMod p`. -/
lemma sum_Icc_castZMod {M : Type*} [AddCommMonoid M] (g : ZMod p → M) :
    ∑ i ∈ Finset.Icc 1 (p - 1), g (i : ZMod p) =
      ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), g x := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro x hx
    rw [Finset.mem_erase] at hx
    rw [Finset.mem_Icc]
    have hval : x.val < p := ZMod.val_lt x
    have hpos : 0 < x.val := ZMod.val_pos.mpr hx.1
    exact ⟨hpos, Nat.le_sub_one_of_lt hval⟩
  · intro a ha
    rw [Finset.mem_Icc] at ha
    exact ZMod.val_cast_of_lt (by omega)
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro a _; rfl

/-- Power sum of `x⁻¹` over the nonzero elements of a finite field vanishes for
`1 ≤ κ < |K|-1`. -/
lemma sum_erase_inv_pow_eq_zero (κ : ℕ) (hκ1 : 1 ≤ κ) (hκ2 : κ < p - 1) :
    ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹) ^ κ = 0 := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  -- include 0 back (its term is 0)
  have h0 : (0 : ZMod p)⁻¹ ^ κ = 0 := by
    rw [inv_zero, zero_pow (by omega)]
  have hsplit : ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹) ^ κ
      = ∑ x : ZMod p, (x⁻¹) ^ κ := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : ZMod p)), h0, add_zero]
  -- reindex by inv (involution)
  have hbij : ∑ x : ZMod p, (x⁻¹) ^ κ = ∑ x : ZMod p, x ^ κ := by
    refine Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹) (fun _ _ => Finset.mem_univ _)
      (fun _ _ => Finset.mem_univ _) (fun a _ => inv_inv a) (fun a _ => inv_inv a) ?_
    intro a _; rfl
  have hcard : Fintype.card (ZMod p) - 1 = p - 1 := by rw [ZMod.card]
  calc ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹) ^ κ
      = ∑ x : ZMod p, (x⁻¹) ^ κ := hsplit
    _ = ∑ x : ZMod p, x ^ κ := hbij
    _ = 0 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) κ (by rw [hcard]; exact hκ2)

/-- The p-adic harmonic sum `Hz κ = ∑_{i=1}^{p-1} i^{-κ}` in `ℤ_[p]`. -/
noncomputable def Hz (κ : ℕ) : ℤ_[p] := ∑ i ∈ Finset.Icc 1 (p - 1), (iv i) ^ κ

lemma norm_Hz_le_one (κ : ℕ) : ‖(Hz κ : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _

lemma toZMod_iv {i : ℕ} (h : ¬ p ∣ i) :
    PadicInt.toZMod (iv i) = ((i : ZMod p))⁻¹ := by
  have hi1 : PadicInt.toZMod (iv i) * (i : ZMod p) = 1 := by
    have h2 := congrArg PadicInt.toZMod (iv_mul_cancel h)
    rw [map_mul, map_one, map_natCast] at h2
    exact h2
  have hne : (i : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact h
  calc PadicInt.toZMod (iv i)
      = PadicInt.toZMod (iv i) * ((i : ZMod p) * (i : ZMod p)⁻¹) := by
        rw [mul_inv_cancel₀ hne, mul_one]
    _ = (PadicInt.toZMod (iv i) * (i : ZMod p)) * (i : ZMod p)⁻¹ := by ring
    _ = (i : ZMod p)⁻¹ := by rw [hi1, one_mul]

/-- Reduction mod `p` of `Hz κ`. -/
lemma toZMod_Hz (κ : ℕ) :
    PadicInt.toZMod (Hz κ) = ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ κ := by
  rw [Hz, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  rw [map_pow, toZMod_iv hnd]

/-- `Hz κ` is divisible by `p` for `1 ≤ κ < p - 1` (power-sum vanishing). -/
lemma dvd_Hz {κ : ℕ} (hκ1 : 1 ≤ κ) (hκ2 : κ < p - 1) : (p : ℤ_[p]) ∣ Hz κ := by
  apply dvd_of_toZMod_zero
  rw [toZMod_Hz]
  calc ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ κ
      = ∑ x ∈ Finset.univ.erase (0 : ZMod p), (x⁻¹) ^ κ :=
        sum_Icc_castZMod (fun x => (x⁻¹) ^ κ)
    _ = 0 := sum_erase_inv_pow_eq_zero κ hκ1 hκ2

/-- Convenience: the mod-`p` vanishing of inverse power sums over `Icc 1 (p-1)`. -/
lemma sum_Icc_inv_pow_zero {κ : ℕ} (hκ1 : 1 ≤ κ) (hκ2 : κ < p - 1) :
    ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ κ = 0 :=
  (sum_Icc_castZMod (fun x => (x⁻¹) ^ κ)).trans (sum_erase_inv_pow_eq_zero κ hκ1 hκ2)

/-- The "paired" sum used in the Wolstenholme argument. -/
noncomputable def Tsum : ℤ_[p] := ∑ i ∈ Finset.Icc 1 (p - 1), iv i * iv (p - i)

/-- Pairing identity `i⁻¹ + (p-i)⁻¹ = p · (i⁻¹ (p-i)⁻¹)`. -/
lemma pair_term {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ p - 1) :
    iv i + iv (p - i) = (p : ℤ_[p]) * (iv i * iv (p - i)) := by
  have hip : i ≤ p := by omega
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hnd' : ¬ p ∣ (p - i) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have ha : (i : ℤ_[p]) * iv i = 1 := mul_iv_cancel hnd
  have hb : ((p - i : ℕ) : ℤ_[p]) * iv (p - i) = 1 := mul_iv_cancel hnd'
  have hab : (i : ℤ_[p]) + ((p - i : ℕ) : ℤ_[p]) = (p : ℤ_[p]) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' hip]
  linear_combination (-(iv (p - i))) * ha + (-(iv i)) * hb +
    (iv i * iv (p - i)) * hab

/-- Reflection `∑ (p-i)⁻¹ = ∑ i⁻¹`. -/
lemma sum_iv_reflect :
    ∑ i ∈ Finset.Icc 1 (p - 1), iv (p := p) (p - i) = ∑ i ∈ Finset.Icc 1 (p - 1), iv (p := p) i := by
  refine Finset.sum_nbij' (fun i => p - i) (fun i => p - i) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; show p - (p - a) = a; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; show p - (p - a) = a; omega
  · intro a ha; rfl

/-- `2 · Hz 1 = p · Tsum`. -/
lemma two_Hz_one : (2 : ℤ_[p]) * Hz 1 = (p : ℤ_[p]) * Tsum := by
  have hHz : Hz 1 = ∑ i ∈ Finset.Icc 1 (p - 1), iv (p := p) i := by
    rw [Hz]; exact Finset.sum_congr rfl (fun i _ => pow_one _)
  rw [hHz, Tsum]
  calc (2 : ℤ_[p]) * ∑ i ∈ Finset.Icc 1 (p - 1), iv i
      = (∑ i ∈ Finset.Icc 1 (p - 1), iv i) + (∑ i ∈ Finset.Icc 1 (p - 1), iv i) := by
        rw [two_mul]
    _ = (∑ i ∈ Finset.Icc 1 (p - 1), iv i) + (∑ i ∈ Finset.Icc 1 (p - 1), iv (p - i)) := by
        rw [sum_iv_reflect]
    _ = ∑ i ∈ Finset.Icc 1 (p - 1), (iv i + iv (p - i)) := by rw [← Finset.sum_add_distrib]
    _ = ∑ i ∈ Finset.Icc 1 (p - 1), (p : ℤ_[p]) * (iv i * iv (p - i)) :=
        Finset.sum_congr rfl (fun i hi => by
          rw [Finset.mem_Icc] at hi; exact pair_term hi.1 hi.2)
    _ = (p : ℤ_[p]) * ∑ i ∈ Finset.Icc 1 (p - 1), (iv i * iv (p - i)) := by rw [Finset.mul_sum]

/-- `p ∣ Tsum`. -/
lemma dvd_Tsum (hp5 : 5 ≤ p) : (p : ℤ_[p]) ∣ Tsum := by
  apply dvd_of_toZMod_zero
  rw [Tsum, map_sum]
  have hterm : ∀ i ∈ Finset.Icc 1 (p - 1),
      PadicInt.toZMod (iv i * iv (p - i)) = -(((i : ZMod p)⁻¹) ^ 2) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hnd' : ¬ p ∣ (p - i) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    rw [map_mul, toZMod_iv hnd, toZMod_iv hnd']
    have hcast : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [hcast, inv_neg]; ring
  rw [Finset.sum_congr rfl hterm]
  have h0 := sum_Icc_inv_pow_zero (p := p) (κ := 2) (by norm_num) (by omega)
  calc ∑ i ∈ Finset.Icc 1 (p - 1), -(((i : ZMod p)⁻¹) ^ 2)
      = -(∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ 2) := by rw [Finset.sum_neg_distrib]
    _ = 0 := by rw [h0, neg_zero]

/-- **Wolstenholme (order 2 part):** `p² ∣ Hz 1` for `p ≥ 5`. -/
lemma dvd_sq_Hz_one (hp5 : 5 ≤ p) : (p : ℤ_[p]) ^ 2 ∣ Hz 1 := by
  obtain ⟨s, hs⟩ := dvd_Tsum hp5
  have h2 : (2 : ℤ_[p]) * Hz 1 = (p : ℤ_[p]) ^ 2 * s := by
    rw [two_Hz_one, hs]; ring
  have hu : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    have hcast : ((2 : ℕ) : ℤ_[p]) = 2 := by norm_cast
    rw [← hcast]
    exact norm_cast_eq_one (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  refine ⟨w * s, ?_⟩
  calc Hz 1 = w * ((2 : ℤ_[p]) * Hz 1) := by
        rw [← mul_assoc, mul_comm w (2 : ℤ_[p]), hw, one_mul]
    _ = w * ((p : ℤ_[p]) ^ 2 * s) := by rw [h2]
    _ = (p : ℤ_[p]) ^ 2 * (w * s) := by ring

/-- **Wolstenholme (order 1 part):** `p ∣ Hz 2` for `p ≥ 5`. -/
lemma dvd_Hz_two (hp5 : 5 ≤ p) : (p : ℤ_[p]) ∣ Hz 2 :=
  dvd_Hz (by norm_num) (by omega)

/-! ## The block factor `1 + w t` and the bound `padicLog (w t) ∈ p³ ℤ_[p]` -/

omit hp in
/-- For `p ≥ 5` and `v ≥ 1`, `v + 3 ≤ p^v`. -/
lemma pow_ge (hp5 : 5 ≤ p) : ∀ v : ℕ, 1 ≤ v → v + 3 ≤ p ^ v := by
  intro v
  induction v with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simpa using (by omega : 4 ≤ p)
    · have hih := ih hm
      have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
      have hps : p ^ (m + 1) = p * p ^ m := by rw [pow_succ, mul_comm]
      nlinarith [hih, hpm, hps]

omit hp in
/-- For `p ≥ 5` and `κ ≥ 3`, `v_p(κ) ≤ κ - 3`. -/
lemma padicVal_le_sub_three (hp5 : 5 ≤ p) {κ : ℕ} (hκ : 3 ≤ κ) :
    padicValNat p κ ≤ κ - 3 := by
  have hpv : p ^ (padicValNat p κ) ≤ κ := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  rcases Nat.eq_zero_or_pos (padicValNat p κ) with h0 | hpos
  · omega
  · have := pow_ge hp5 (padicValNat p κ) hpos
    omega

/-- A public copy of the `n`-th term of the log series. -/
noncomputable def logT (x : ℤ_[p]) (n : ℕ) : ℚ_[p] :=
  (-1) ^ n * (x : ℚ_[p]) ^ (n + 1) / (n + 1)

lemma padicLog_eq_logT (x : ℤ_[p]) : padicLog x = ∑' n, logT x n := rfl

lemma summable_logT (x : ℤ_[p]) (hx : ‖x‖ < 1) : Summable (logT x) :=
  summable_logTerm x hx

/-- The block factor `1 + w_t = ∏_{i=1}^{p-1}(1 + t p / i)`, term by term. -/
noncomputable def wfac (t i : ℕ) : ℤ_[p] := (↑(t * p) : ℤ_[p]) * iv i

lemma norm_wfac_le (t i : ℕ) : ‖(wfac t i : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  rw [wfac, norm_mul]
  calc ‖(↑(t * p) : ℤ_[p])‖ * ‖iv i‖
      ≤ ‖(↑(t * p) : ℤ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ = ‖(↑(t * p) : ℤ_[p])‖ := mul_one _
    _ ≤ (p : ℝ)⁻¹ := by
        rw [Nat.cast_mul, norm_mul, ← PadicInt.norm_p (p := p)]
        exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)

lemma norm_wfac_lt (hp5 : 5 ≤ p) (t i : ℕ) : ‖(wfac t i : ℤ_[p])‖ < 1 := by
  refine lt_of_le_of_lt (norm_wfac_le t i) ?_
  rw [inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
  exact_mod_cast (by omega : 1 < p)

lemma coe_wfac {t i : ℕ} (h : ¬ p ∣ i) :
    ((wfac t i : ℤ_[p]) : ℚ_[p]) = (↑(t * p) : ℚ_[p]) * (↑i)⁻¹ := by
  rw [wfac]
  push_cast [coe_iv h]
  ring

/-- `1 + w t = ∏_i (1 + wfac t i)`. -/
noncomputable def oneAddW (t : ℕ) : ℤ_[p] := ∏ i ∈ Finset.Icc 1 (p - 1), (1 + wfac t i)

/-- `w t = ∏_i (1 + wfac t i) - 1`. -/
noncomputable def w (t : ℕ) : ℤ_[p] := oneAddW t - 1

lemma coe_Hz (κ : ℕ) :
    ((Hz κ : ℤ_[p]) : ℚ_[p]) = ∑ i ∈ Finset.Icc 1 (p - 1), ((↑i : ℚ_[p])⁻¹) ^ κ := by
  rw [Hz, PadicInt.coe_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  rw [PadicInt.coe_pow, coe_iv hnd]

/-- Regrouped `n`-th term of `∑_i padicLog (wfac t i)`, with the harmonic sum factored out. -/
lemma term_val (t n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac t i) n
      = (-1) ^ n * (↑(t * p) : ℚ_[p]) ^ (n + 1) / ((n : ℚ_[p]) + 1) * ((Hz (n + 1) : ℤ_[p]) : ℚ_[p]) := by
  rw [coe_Hz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  rw [logT, coe_wfac hnd, mul_pow]
  ring

/-- `‖(t p : ℚ_[p])‖ ≤ p⁻¹`. -/
lemma norm_natCast_tp_le (t : ℕ) : ‖(↑(t * p) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  rw [← PadicInt.coe_natCast, PadicInt.padic_norm_e_of_padicInt]
  rw [Nat.cast_mul, norm_mul, ← PadicInt.norm_p (p := p)]
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)

/-- `‖n+1‖⁻¹ = p^{v_p(n+1)}`. -/
lemma norm_natCast_succ_inv (n : ℕ) :
    ‖((n : ℚ_[p]) + 1)‖⁻¹ = (p : ℝ) ^ (padicValNat p (n + 1) : ℤ) := by
  have hm0 : ((n + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hcast : ((n : ℚ_[p]) + 1) = ((n + 1 : ℕ) : ℚ_[p]) := by push_cast; ring
  rw [hcast, Padic.norm_eq_zpow_neg_valuation hm0, Padic.valuation_natCast,
    zpow_neg, inv_inv]

/-- `‖Hz 1‖ ≤ p^{-2}`. -/
lemma norm_Hz_one_le (hp5 : 5 ≤ p) : ‖(Hz 1 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-2 : ℤ) := by
  have := (dvd_iff_norm_le (Hz 1) 2).mp (dvd_sq_Hz_one hp5)
  simpa using this

/-- `‖Hz 2‖ ≤ p^{-1}`. -/
lemma norm_Hz_two_le (hp5 : 5 ≤ p) : ‖(Hz 2 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
  have hd : (p : ℤ_[p]) ^ 1 ∣ Hz 2 := by rw [pow_one]; exact dvd_Hz_two hp5
  have := (dvd_iff_norm_le (Hz 2) 1).mp hd
  simpa using this

/-- The core `p^{-3}` estimate on the harmonic-weighted power factor. -/
lemma harmonic_factor_bound (hp5 : 5 ≤ p) (n : ℕ) :
    (p : ℝ) ^ (-(↑(n + 1)) : ℤ) * (p : ℝ) ^ (padicValNat p (n + 1) : ℤ) * ‖(Hz (n + 1) : ℤ_[p])‖
      ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set v : ℤ := (padicValNat p (n + 1) : ℤ) with hv
  -- combine the two powers of p
  have hcomb : (p : ℝ) ^ (-(↑(n + 1)) : ℤ) * (p : ℝ) ^ v
      = (p : ℝ) ^ (v - (↑(n + 1))) := by
    rw [← zpow_add₀ (ne_of_gt hp0)]; ring_nf
  rw [hcomb]
  match n, (rfl : n = n) with
  | 0, _ =>
    have hH : ‖(Hz 1 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-2 : ℤ) := norm_Hz_one_le hp5
    have hvv : v = 0 := by rw [hv]; norm_num [padicValNat.one]
    calc (p : ℝ) ^ (v - (↑(0 + 1))) * ‖(Hz (0 + 1) : ℤ_[p])‖
        ≤ (p : ℝ) ^ (v - (↑(0 + 1))) * (p : ℝ) ^ (-2 : ℤ) := by
          apply mul_le_mul_of_nonneg_left hH (by positivity)
      _ = (p : ℝ) ^ (-3 : ℤ) := by
          rw [← zpow_add₀ (ne_of_gt hp0)]; rw [hvv]; norm_num
  | 1, _ =>
    have hH : ‖(Hz 2 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-1 : ℤ) := norm_Hz_two_le hp5
    have hvv : v = 0 := by
      have h2 : padicValNat p 2 = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
      rw [hv]; norm_num [h2]
    calc (p : ℝ) ^ (v - (↑(1 + 1))) * ‖(Hz (1 + 1) : ℤ_[p])‖
        ≤ (p : ℝ) ^ (v - (↑(1 + 1))) * (p : ℝ) ^ (-1 : ℤ) := by
          apply mul_le_mul_of_nonneg_left hH (by positivity)
      _ = (p : ℝ) ^ (-3 : ℤ) := by
          rw [← zpow_add₀ (ne_of_gt hp0)]; rw [hvv]; norm_num
  | (m + 2), _ =>
    have hH : ‖(Hz (m + 2 + 1) : ℤ_[p])‖ ≤ 1 := norm_Hz_le_one _
    have hexp : v - (↑(m + 2 + 1)) ≤ (-3 : ℤ) := by
      have hle : padicValNat p (m + 2 + 1) ≤ (m + 2 + 1) - 3 :=
        padicVal_le_sub_three hp5 (by omega)
      rw [hv]; omega
    calc (p : ℝ) ^ (v - (↑(m + 2 + 1))) * ‖(Hz (m + 2 + 1) : ℤ_[p])‖
        ≤ (p : ℝ) ^ (v - (↑(m + 2 + 1))) * 1 := by
          apply mul_le_mul_of_nonneg_left hH (by positivity)
      _ = (p : ℝ) ^ (v - (↑(m + 2 + 1))) := mul_one _
      _ ≤ (p : ℝ) ^ (-3 : ℤ) := zpow_le_zpow_right₀ hp1 hexp

/-- Each regrouped term has norm `≤ p^{-3}`. -/
lemma norm_term_le (hp5 : 5 ≤ p) (t n : ℕ) :
    ‖∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac (p := p) t i) n‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  rw [term_val]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnorm : ‖(-1 : ℚ_[p]) ^ n * (↑(t * p)) ^ (n + 1) / ((n : ℚ_[p]) + 1) *
        ((Hz (n + 1) : ℤ_[p]) : ℚ_[p])‖
      = ‖(↑(t * p) : ℚ_[p])‖ ^ (n + 1) * ‖((n : ℚ_[p]) + 1)‖⁻¹ * ‖(Hz (n + 1) : ℤ_[p])‖ := by
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, PadicInt.padic_norm_e_of_padicInt, div_eq_mul_inv]
  rw [hnorm, norm_natCast_succ_inv]
  -- now bound
  have hApow : ‖(↑(t * p) : ℚ_[p])‖ ^ (n + 1) ≤ (p : ℝ) ^ (-(↑(n + 1)) : ℤ) := by
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_natCast_tp_le t) (n + 1)) ?_
    rw [inv_pow, ← zpow_natCast (p : ℝ) (n + 1), ← zpow_neg]
  calc ‖(↑(t * p) : ℚ_[p])‖ ^ (n + 1) * (p : ℝ) ^ (padicValNat p (n + 1) : ℤ) *
        ‖(Hz (n + 1) : ℤ_[p])‖
      ≤ (p : ℝ) ^ (-(↑(n + 1)) : ℤ) * (p : ℝ) ^ (padicValNat p (n + 1) : ℤ) *
          ‖(Hz (n + 1) : ℤ_[p])‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_right hApow (by positivity)
    _ ≤ (p : ℝ) ^ (-3 : ℤ) := harmonic_factor_bound hp5 n

/-- **Key bound:** `padicLog (w t) ∈ p³ ℤ_[p]`, i.e. `‖padicLog (w t)‖ ≤ p^{-3}`. -/
lemma norm_padicLog_w_le (hp5 : 5 ≤ p) (t : ℕ) :
    ‖padicLog (w (p := p) t)‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp3 : 3 ≤ p := by omega
  have hwfac_lt : ∀ i ∈ Finset.Icc 1 (p - 1), ‖(wfac t i : ℤ_[p])‖ < 1 :=
    fun i _ => norm_wfac_lt hp5 t i
  have hlog : padicLog (w (p := p) t) = ∑ i ∈ Finset.Icc 1 (p - 1), padicLog (wfac t i) := by
    rw [w, oneAddW]; exact padicLog_prod hp3 _ _ hwfac_lt
  have hsummable : ∀ i ∈ Finset.Icc 1 (p - 1), Summable (fun n => logT (wfac t i) n) :=
    fun i _ => summable_logT (wfac t i) (norm_wfac_lt hp5 t i)
  have hlog2 : padicLog (w (p := p) t)
      = ∑' n, ∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac t i) n := by
    rw [hlog,
      show (∑ i ∈ Finset.Icc 1 (p - 1), padicLog (wfac t i))
          = ∑ i ∈ Finset.Icc 1 (p - 1), ∑' n, logT (wfac t i) n from
        Finset.sum_congr rfl (fun i _ => padicLog_eq_logT _)]
    exact (Summable.tsum_finsetSum hsummable).symm
  rw [hlog2]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    (fun n => norm_term_le hp5 t n)

/-! ## The p-free factorial `W(m)` and its block decomposition -/

/-- `(p-1)!` in `ℤ_[p]`. -/
noncomputable def factp : ℤ_[p] := ∏ i ∈ Finset.Icc 1 (p - 1), (↑i : ℤ_[p])

/-- The `t`-th block product `∏_{i=1}^{p-1} (t p + i)`. -/
noncomputable def Pblock (t : ℕ) : ℤ_[p] := ∏ i ∈ Finset.Icc 1 (p - 1), (↑(t * p + i) : ℤ_[p])

/-- `W(m) = ∏_{1 ≤ j ≤ m, p ∤ j} j`. -/
noncomputable def Wfac (m : ℕ) : ℤ_[p] :=
  ∏ j ∈ (Finset.Icc 1 m).filter (fun j => ¬ p ∣ j), (↑j : ℤ_[p])

lemma norm_factp : ‖(factp : ℤ_[p])‖ = 1 := by
  rw [factp, norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact norm_cast_eq_one (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)

lemma isUnit_factp : IsUnit (factp : ℤ_[p]) := PadicInt.isUnit_iff.mpr norm_factp

lemma Pblock_eq (t : ℕ) : (Pblock t : ℤ_[p]) = factp * oneAddW t := by
  rw [factp, oneAddW, ← Finset.prod_mul_distrib, Pblock]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  rw [wfac]
  push_cast
  have hiv : (↑i : ℤ_[p]) * iv i = 1 := mul_iv_cancel hnd
  linear_combination (-((t : ℤ_[p]) * (p : ℤ_[p]))) * hiv

/-- **Block decomposition:** `W(p·N) = ∏_{t<N} Pblock t`. -/
lemma Wfac_block (N : ℕ) : (Wfac (p * N) : ℤ_[p]) = ∏ t ∈ Finset.range N, Pblock t := by
  have hp0 : 0 < p := hp.out.pos
  rw [Wfac, Nat.mul_comm p N]
  simp only [Pblock]
  rw [← Finset.prod_product']
  refine (Finset.prod_nbij' (fun x => x.1 * p + x.2) (fun n => (n / p, n % p)) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨t, i⟩ hx
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨ht, hi1, hi2⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have hbound : (t + 1) * p ≤ N * p := mul_le_mul_right' (by omega) p
      have : t * p + p ≤ N * p := by rw [add_mul, one_mul] at hbound; exact hbound
      omega
    · intro hd
      have hpi : p ∣ i := (Nat.dvd_add_right (dvd_mul_left p t)).mp hd
      have := Nat.le_of_dvd (by omega) hpi
      omega
  · rintro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hnd⟩ := hn
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    have hmod : n % p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hmodlt : n % p < p := Nat.mod_lt n hp0
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hp0]
      rcases lt_or_eq_of_le hn2 with hlt | heq
      · exact hlt
      · exact absurd (heq.symm ▸ dvd_mul_left p N) hnd
    · omega
    · omega
  · rintro ⟨t, i⟩ hx
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨ht, hi1, hi2⟩ := hx
    have hmod : (t * p + i) % p = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt (by omega)
    have hdiv : (t * p + i) / p = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
    simp [hmod, hdiv]
  · rintro n hn
    show n / p * p + n % p = n
    rw [Nat.mul_comm (n / p) p]
    exact Nat.div_add_mod n p
  · rintro ⟨t, i⟩ _; rfl

/-! ## Final assembly: the balanced supercongruence mod `p³` -/

/-- Ultrametric triangle inequality for subtraction in `ℤ_[p]`. -/
lemma norm_sub_le_max' (a b : ℤ_[p]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max a (-b)).trans ?_
  rw [norm_neg]

lemma norm_w_lt (hp5 : 5 ≤ p) (t : ℕ) : ‖(w (p := p) t)‖ < 1 := by
  rw [w, oneAddW]
  exact norm_prod_one_add_sub_one_lt _ _ (fun i _ => norm_wfac_lt hp5 t i)

/-- The product over a family `s` of `∏_{t < cnt a} (1 + w t)`, i.e. the analytic
part of `∏ W(c_a · W)`. -/
noncomputable def Aprod {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) : ℤ_[p] :=
  ∏ a ∈ s, ∏ t ∈ Finset.range (cnt a), oneAddW t

lemma Aprod_eq_sigma {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    Aprod (p := p) s cnt = ∏ x ∈ s.sigma (fun a => Finset.range (cnt a)), (1 + w (p := p) x.2) := by
  rw [Aprod, Finset.prod_sigma]
  apply Finset.prod_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro t _
  rw [w]; ring

lemma padicLog_Aprod (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    padicLog (Aprod (p := p) s cnt - 1)
      = ∑ x ∈ s.sigma (fun a => Finset.range (cnt a)), padicLog (w (p := p) x.2) := by
  rw [Aprod_eq_sigma]
  exact padicLog_prod (by omega) _ _ (fun x _ => norm_w_lt hp5 x.2)

lemma norm_Aprod_sub_one_lt (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    ‖Aprod (p := p) s cnt - 1‖ < 1 := by
  rw [Aprod_eq_sigma]
  exact norm_prod_one_add_sub_one_lt _ _ (fun x _ => norm_w_lt hp5 x.2)

lemma norm_padicLog_Aprod_le (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    ‖padicLog (Aprod (p := p) s cnt - 1)‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  rw [padicLog_Aprod hp5]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    (fun x _ => norm_padicLog_w_le hp5 x.2)

/-- If `u, v` are close to `1` and their logs are both divisible by `p³`, then `p³ ∣ u - v`. -/
lemma dvd_sub_of_logs (hp5 : 5 ≤ p) (u v : ℤ_[p])
    (hu : ‖u - 1‖ < 1) (hv : ‖v - 1‖ < 1)
    (hlu : ‖padicLog (u - 1)‖ ≤ (p : ℝ) ^ (-3 : ℤ))
    (hlv : ‖padicLog (v - 1)‖ ≤ (p : ℝ) ^ (-3 : ℤ)) :
    (p : ℤ_[p]) ^ 3 ∣ (u - v) := by
  have hp3 : 3 ≤ p := by omega
  -- v is a unit
  have hvnorm : ‖v‖ = 1 := by
    have : ‖v‖ = ‖(v - 1) + 1‖ := by ring_nf
    rw [this]
    have h1 : ‖((1 : ℤ_[p]))‖ = 1 := norm_one
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := v - 1) (y := (1 : ℤ_[p])) (by rw [h1]; exact ne_of_lt hv)
    rw [this, h1]
    exact max_eq_right (le_of_lt hv)
  set vinv : ℤ_[p] := PadicInt.inv v with hvinv
  have hvvinv : v * vinv = 1 := PadicInt.mul_inv hvnorm
  set r : ℤ_[p] := u * vinv with hr
  -- r - 1 = (u - v) * vinv
  have hrsub : r - 1 = (u - v) * vinv := by
    rw [hr]
    have : u * vinv - 1 = u * vinv - v * vinv := by rw [hvvinv]
    rw [this]; ring
  have hvinv_norm : ‖vinv‖ = 1 := by
    have := congrArg norm hvvinv
    rw [norm_mul, hvnorm, one_mul, norm_one] at this
    exact this
  have huvnorm : ‖u - v‖ < 1 := by
    calc ‖u - v‖ = ‖(u - 1) - (v - 1)‖ := by ring_nf
      _ ≤ max ‖u - 1‖ ‖v - 1‖ := norm_sub_le_max' _ _
      _ < 1 := max_lt hu hv
  have hrsubnorm : ‖r - 1‖ < 1 := by
    rw [hrsub, norm_mul, hvinv_norm, mul_one]; exact huvnorm
  -- padicLog r = padicLog u - padicLog v via padicLog_mul with x=r-1, y=v-1
  have hrv : r * v = u := by rw [hr]; rw [mul_assoc, mul_comm vinv v, hvvinv, mul_one]
  have hmul := padicLog_mul hp3 (r - 1) (v - 1) hrsubnorm hv
  have hexp : (r - 1) + (v - 1) + (r - 1) * (v - 1) = r * v - 1 := by ring
  rw [hexp, hrv] at hmul
  -- so padicLog (u - 1) = padicLog (r - 1) + padicLog (v - 1)
  have hlogr : padicLog (r - 1) = padicLog (u - 1) - padicLog (v - 1) := by
    rw [hmul]; ring
  have hlogr_le : ‖padicLog (r - 1)‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
    rw [hlogr]
    calc ‖padicLog (u - 1) - padicLog (v - 1)‖
        ≤ max ‖padicLog (u - 1)‖ ‖padicLog (v - 1)‖ := by
          rw [sub_eq_add_neg]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])
      _ ≤ (p : ℝ) ^ (-3 : ℤ) := max_le hlu hlv
  have hdvd : (p : ℤ_[p]) ^ 3 ∣ (r - 1) :=
    sub_one_dvd_of_padicLog hp3 r hrsubnorm 3 (by simpa using hlogr_le)
  -- u - v = (r - 1) * v
  have huv : u - v = (r - 1) * v := by
    rw [hrsub, mul_assoc]
    rw [show vinv * v = 1 from by rw [mul_comm]; exact hvvinv, mul_one]
  rw [huv]
  exact hdvd.mul_right v

/-- `∏_{i∈s} W(c_i · W) = factp^(∑ c_i M') · Aprod s (c · M')` when `W = p · M'`. -/
lemma Wprod_eq {ι : Type*} (Wn M' : ℕ) (hWeq : Wn = p * M')
    (s : Finset ι) (c : ι → ℕ) :
    (∏ i ∈ s, Wfac (c i * Wn))
      = (factp : ℤ_[p]) ^ (∑ i ∈ s, c i * M') * Aprod (p := p) s (fun i => c i * M') := by
  rw [Aprod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hci : c i * Wn = p * (c i * M') := by rw [hWeq]; ring
  rw [hci, Wfac_block]
  rw [show (∏ t ∈ Finset.range (c i * M'), Pblock t)
      = ∏ t ∈ Finset.range (c i * M'), (factp * oneAddW t) from
    Finset.prod_congr rfl (fun t _ => Pblock_eq t)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- **Balanced supercongruence (mod `p³`).**
For a prime `p ≥ 5`, positive coefficients `c`, sign split into `num`/`den`, `p ∣ W`
and balanced condition `∑_num c = ∑_den c`, we have
`p³ ∣ (∏_{num} W(c_i·W) - ∏_{den} W(c_i·W))`. -/
theorem balanced_supercongruence (hp5 : 5 ≤ p) {ι : Type*}
    (num den : Finset ι) (c : ι → ℕ) (Wn : ℕ) (hW : p ∣ Wn)
    (hbal : ∑ i ∈ num, c i = ∑ i ∈ den, c i) :
    (p : ℤ_[p]) ^ 3 ∣ ((∏ i ∈ num, Wfac (c i * Wn)) - (∏ i ∈ den, Wfac (c i * Wn))) := by
  obtain ⟨M', hWeq⟩ := hW
  rw [Wprod_eq Wn M' hWeq num c, Wprod_eq Wn M' hWeq den c]
  have hexp : (∑ i ∈ num, c i * M') = (∑ i ∈ den, c i * M') := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hbal]
  rw [hexp, ← mul_sub]
  have hdvd : (p : ℤ_[p]) ^ 3 ∣ (Aprod num (fun i => c i * M') - Aprod den (fun i => c i * M')) :=
    dvd_sub_of_logs hp5 _ _
      (norm_Aprod_sub_one_lt hp5 _ _) (norm_Aprod_sub_one_lt hp5 _ _)
      (norm_padicLog_Aprod_le hp5 _ _) (norm_padicLog_Aprod_le hp5 _ _)
  exact hdvd.mul_left _

end PKaz


end

section  -- ===== VonStaudt =====

namespace VonStaudt

variable {p : ℕ} [hp : Fact p.Prime]

open Finset

/-- For `p ≥ 3` and `k ≥ 1`, we have `k + 2 ≤ p ^ k`. -/
lemma add_two_le_pow (hp3 : 3 ≤ p) : ∀ k : ℕ, 1 ≤ k → k + 2 ≤ p ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge 1 (n + 1) with h | h
    · -- n ≥ 1
      have hn : 1 ≤ n := by omega
      have ihn := ih hn
      have hpow : p ^ (n + 1) = p ^ n * p := by rw [pow_succ]
      have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
      nlinarith [ihn, hpn, hp3]
    · -- n + 1 = 1
      have : n = 0 := by omega
      subst this
      simpa using hp3

/-- For a prime `p ≥ 3` and `l ≥ 2`, `padicValNat p l + 2 ≤ l`. -/
lemma padicValNat_add_two_le (hp3 : 3 ≤ p) {l : ℕ} (hl : 2 ≤ l) :
    padicValNat p l + 2 ≤ l := by
  have hdvd : p ^ padicValNat p l ∣ l := pow_padicValNat_dvd
  have hle : p ^ padicValNat p l ≤ l := Nat.le_of_dvd (by omega) hdvd
  rcases Nat.eq_zero_or_pos (padicValNat p l) with h0 | hpos
  · omega
  · have := add_two_le_pow hp3 (padicValNat p l) hpos
    omega

/-- The `p`-adic norm of a natural number cast is at most `1`. -/
lemma norm_nat_le_one (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := p) (n : ℤ)
  simpa using this

/-- For `l ≠ 0`, the norm of `(l : ℚ_[p])` equals `p ^ (- padicValNat p l)`. -/
lemma norm_natCast_eq (l : ℕ) (hl : l ≠ 0) :
    ‖(l : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p l : ℤ)) := by
  have hne : (l : ℚ_[p]) ≠ 0 := by
    simpa using hl
  rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]

/-- Norm bound for a single correction term (in its "good" form with `m.choose i / (m+1-i)`),
assuming the induction hypothesis for `bernoulli i`. -/
lemma term_norm_le (hp5 : 5 ≤ p) {m i : ℕ} (hi : i < m)
    (ih : ‖((bernoulli i : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)) :
    ‖((bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ) : ℚ)
        : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  set l := m + 1 - i with hl
  have hl2 : 2 ≤ l := by omega
  have hlne : l ≠ 0 := by omega
  set v := padicValNat p l with hv
  have hvle : v + 2 ≤ l := padicValNat_add_two_le (by omega) hl2
  have hcast : ((bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ l / (l : ℚ) : ℚ) : ℚ_[p])
      = ((bernoulli i : ℚ) : ℚ_[p]) * ((m.choose i : ℕ) : ℚ_[p]) * ((p : ℕ) : ℚ_[p]) ^ l
          / ((l : ℕ) : ℚ_[p]) := by
    push_cast
    ring
  have hnl : ‖((l : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-(v : ℤ)) := norm_natCast_eq l hlne
  rw [hcast, norm_div, norm_mul, norm_mul, norm_pow, Padic.norm_p, hnl]
  have hstep : ‖((bernoulli i : ℚ) : ℚ_[p])‖ * ‖((m.choose i : ℕ) : ℚ_[p])‖
      * ((p : ℝ)⁻¹) ^ l / (p : ℝ) ^ (-(v : ℤ))
      ≤ (p : ℝ) * 1 * ((p : ℝ)⁻¹) ^ l / (p : ℝ) ^ (-(v : ℤ)) := by
    gcongr
    exact norm_nat_le_one _
  refine hstep.trans ?_
  rw [zpow_neg, zpow_natCast, inv_pow, mul_one]
  have expand : (p : ℝ) * ((p : ℝ) ^ l)⁻¹ / ((p : ℝ) ^ v)⁻¹
      = (p : ℝ) ^ (v + 1) / (p : ℝ) ^ l := by
    field_simp
    ring
  rw [expand, inv_eq_one_div, div_le_div_iff₀ (by positivity) hpR, one_mul, ← pow_succ]
  exact pow_le_pow_right₀ hp1 (by omega)

/-- Rewriting a Faulhaber correction term into its "good" form. -/
lemma term_eq {m i : ℕ} (hi : i ≤ m) :
    bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1)
      = bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ) := by
  have hd1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hd2 : ((m + 1 - i : ℕ) : ℚ) ≠ 0 := by
    have : 0 < m + 1 - i := by omega
    exact_mod_cast this.ne'
  have hid : (m.choose i : ℚ) * ((m : ℚ) + 1)
      = ((m + 1).choose i : ℚ) * ((m + 1 - i : ℕ) : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_mul_succ_eq m i)
    push_cast at h
    linarith [h]
  rw [show bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1)
        = bernoulli i * (p : ℚ) ^ (m + 1 - i) * (((m + 1).choose i : ℚ) / ((m : ℚ) + 1)) by ring,
      show bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ)
        = bernoulli i * (p : ℚ) ^ (m + 1 - i)
            * ((m.choose i : ℚ) / ((m + 1 - i : ℕ) : ℚ)) by ring]
  congr 1
  rw [div_eq_div_iff hd1 hd2]
  linarith [hid]

/-- The key equation `(★)`: for `m ≥ 1`,
`bernoulli m * p = (∑_{k<p} k^m) - ∑_{i<m} (good-form correction term)`. -/
lemma key_eq (m : ℕ) (hm : 1 ≤ m) :
    bernoulli m * (p : ℚ)
      = (∑ k ∈ range p, (k : ℚ) ^ m)
        - ∑ i ∈ range m,
            bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ) := by
  have hfaul := sum_range_pow p m
  rw [Finset.sum_range_succ] at hfaul
  have hlast : bernoulli m * ((m + 1).choose m : ℚ) * (p : ℚ) ^ (m + 1 - m) / ((m : ℚ) + 1)
      = bernoulli m * (p : ℚ) := by
    rw [Nat.choose_succ_self_right, show m + 1 - m = 1 by omega]
    push_cast
    field_simp
  have hcongr : (∑ i ∈ range m,
        bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1))
      = ∑ i ∈ range m,
          bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m + 1 - i : ℕ) : ℚ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact term_eq (Nat.le_of_lt (Finset.mem_range.mp hi))
  rw [hlast, hcongr] at hfaul
  linarith [hfaul]

/-- The power sum over `range p` equals the sum over all of `ZMod p`. -/
lemma sum_range_pow_zmod (m : ℕ) :
    (∑ k ∈ range p, ((k : ℕ) : ZMod p) ^ m) = ∑ x : ZMod p, x ^ m := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine (Finset.sum_bij' (fun x _ => ZMod.val x) (fun k _ => ((k : ℕ) : ZMod p))
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun k _ => Finset.mem_univ _)
    (fun x _ => ZMod.natCast_zmod_val x)
    (fun k hk => ZMod.val_cast_of_lt (Finset.mem_range.mp hk)) ?_).symm
  intro x _
  rw [ZMod.natCast_zmod_val]

/-- For `m ≥ 1` with `(p - 1) ∤ m`, the sum of `m`-th powers over `ZMod p` vanishes. -/
lemma sum_pow_univ_zmod (m : ℕ) (hm : 1 ≤ m) (hdvd : ¬ (p - 1) ∣ m) :
    (∑ x : ZMod p, x ^ m) = 0 := by
  classical
  have hzero : ∑ x : ZMod p, x ^ m = ∑ x ∈ (univ \ {0} : Finset (ZMod p)), x ^ m := by
    rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))), Finset.sum_singleton,
      zero_pow (by omega : m ≠ 0), add_zero]
  rw [hzero]
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using isUnit_iff_ne_zero
  rw [← hmap, Finset.sum_map]
  simp only [φ, Function.Embedding.coeFn_mk]
  rw [FiniteField.sum_pow_units (ZMod p) m, ZMod.card, if_neg hdvd]

/-- Extract a lower bound on `padicValRat` from an upper bound on the `ℚ_[p]`-norm. -/
private lemma valRat_ge_of_norm_le {q : ℚ} {n : ℤ} (hq : q ≠ 0)
    (h : ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n)) : n ≤ padicValRat p q := by
  have hne : ((q : ℚ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hq
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_ratCast] at h
  rw [zpow_le_zpow_iff_right₀ hp1] at h
  omega

/-- **von Staudt–Clausen valuation bound (ℚ_[p]-norm form).** For an odd prime `p ≥ 5`,
`‖bernoulli m‖_p ≤ p`. -/
theorem norm_bernoulli_le (hp5 : 5 ≤ p) (m : ℕ) :
    ‖((bernoulli m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hpR : (0 : ℝ) < (p : ℝ) := by
      have : (0 : ℕ) < p := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have : (1 : ℕ) ≤ p := by omega
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- m = 0
      rw [bernoulli_zero]
      simpa using hp1
    · -- m ≥ 1
      -- bound on the power sum `S`
      have hS : ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])‖ ≤ 1 := by
        rw [Rat.cast_sum]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) ?_
        intro k _
        rw [Rat.cast_pow, Rat.cast_natCast, norm_pow]
        calc ‖(k : ℚ_[p])‖ ^ m ≤ 1 ^ m := by gcongr; exact norm_nat_le_one k
          _ = 1 := one_pow m
      -- bound on the correction sum
      have hC : ‖((∑ i ∈ range m,
            bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
              / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
        rw [Rat.cast_sum]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
        intro i hi
        exact term_norm_le hp5 (Finset.mem_range.mp hi) (ih i (Finset.mem_range.mp hi))
      -- combine using (★)
      have hcast := congrArg (Rat.cast : ℚ → ℚ_[p]) (key_eq (p := p) m hm)
      rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub] at hcast
      have hcombine : ‖((bernoulli m : ℚ) : ℚ_[p]) * (p : ℚ_[p])‖ ≤ 1 := by
        rw [hcast]
        have hmax :
            ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
              - ((∑ i ∈ range m,
                  bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                    / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖
            ≤ max ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])‖
                ‖((∑ i ∈ range m,
                    bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                      / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ := by
          have h := Padic.nonarchimedean
            ((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
            (-((∑ i ∈ range m,
                bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                  / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p]))
          rwa [← sub_eq_add_neg, norm_neg] at h
        refine hmax.trans (max_le hS ?_)
        exact hC.trans (by simpa using (inv_le_one_of_one_le₀ hp1))
      rw [norm_mul, Padic.norm_p, ← div_eq_mul_inv, div_le_one hpR] at hcombine
      exact hcombine

/-- **von Staudt–Clausen: `p`-integrality of Bernoulli numbers (ℚ_[p]-norm form).**
For an odd prime `p ≥ 5` and `(p - 1) ∤ m`, we have `‖bernoulli m‖_p ≤ 1`. -/
theorem norm_bernoulli_le_one_of_not_dvd (hp5 : 5 ≤ p) (m : ℕ) (hdvd : ¬ (p - 1) ∣ m) :
    ‖((bernoulli m : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (dvd_zero _) hdvd
    · exact h
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  -- The power sum `S` is divisible by `p`, so its norm is at most `p⁻¹`.
  have hS : ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    have hnatdvd : p ∣ ∑ k ∈ range p, k ^ m := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [sum_range_pow_zmod]
      exact sum_pow_univ_zmod m hm hdvd
    have hNeq : ((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
        = (((∑ k ∈ range p, k ^ m : ℕ) : ℤ) : ℚ_[p]) := by
      push_cast; ring
    rw [hNeq]
    have hdvd2 : ((p : ℤ) ^ 1) ∣ ((∑ k ∈ range p, k ^ m : ℕ) : ℤ) := by
      simpa using (Int.natCast_dvd_natCast.mpr hnatdvd)
    have key := (Padic.norm_int_le_pow_iff_dvd (p := p)
      ((∑ k ∈ range p, k ^ m : ℕ) : ℤ) 1).mpr hdvd2
    rwa [Nat.cast_one, zpow_neg_one] at key
  -- The correction sum has norm at most `p⁻¹` (using the already-proven bound for `i < m`).
  have hC : ‖((∑ i ∈ range m,
        bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
          / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [Rat.cast_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro i hi
    exact term_norm_le hp5 (Finset.mem_range.mp hi) (norm_bernoulli_le hp5 i)
  -- combine using (★)
  have hcast := congrArg (Rat.cast : ℚ → ℚ_[p]) (key_eq (p := p) m hm)
  rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub] at hcast
  have hcombine : ‖((bernoulli m : ℚ) : ℚ_[p]) * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [hcast]
    have hmax :
        ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
          - ((∑ i ∈ range m,
              bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖
        ≤ max ‖((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])‖
            ‖((∑ i ∈ range m,
                bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
                  / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ := by
      have h := Padic.nonarchimedean
        ((∑ k ∈ range p, (k : ℚ) ^ m : ℚ) : ℚ_[p])
        (-((∑ i ∈ range m,
            bernoulli i * (m.choose i : ℚ) * (p : ℚ) ^ (m + 1 - i)
              / ((m + 1 - i : ℕ) : ℚ) : ℚ) : ℚ_[p]))
      rwa [← sub_eq_add_neg, norm_neg] at h
    exact hmax.trans (max_le hS hC)
  rw [norm_mul, Padic.norm_p] at hcombine
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  exact le_of_mul_le_mul_right (by rwa [one_mul]) hpinv

/-- **von Staudt–Clausen valuation bound.** For an odd prime `p ≥ 5` and any `m`,
`padicValRat p (bernoulli m) ≥ -1`. -/
theorem padicValRat_bernoulli_ge (hp5 : 5 ≤ p) (m : ℕ) :
    (-1 : ℤ) ≤ padicValRat p (bernoulli m) := by
  rcases eq_or_ne (bernoulli m) 0 with h0 | h0
  · rw [h0, padicValRat.zero]; norm_num
  · exact valRat_ge_of_norm_le h0 (by rw [neg_neg, zpow_one]; exact norm_bernoulli_le hp5 m)

/-- **von Staudt–Clausen: `p`-integrality.** For an odd prime `p ≥ 5` and `(p - 1) ∤ m`,
`padicValRat p (bernoulli m) ≥ 0`. -/
theorem padicValRat_bernoulli_nonneg (hp5 : 5 ≤ p) (m : ℕ) (hdvd : ¬ (p - 1) ∣ m) :
    (0 : ℤ) ≤ padicValRat p (bernoulli m) := by
  rcases eq_or_ne (bernoulli m) 0 with h0 | h0
  · rw [h0, padicValRat.zero]
  · exact valRat_ge_of_norm_le h0
      (by rw [neg_zero, zpow_zero]; exact norm_bernoulli_le_one_of_not_dvd hp5 m hdvd)

end VonStaudt

end

section  -- ===== PSigma =====

/-!
# A p-adic vanishing identity: `Σ₂ = 0`

We prove the "second-order coefficient vanishes" identity underlying a
Kazandzidis-type supercongruence, namely that
`∑' m, (-1)^m p^{m+1} Hz(m+1) bernoulli(m) = 0` in `ℚ_[p]` for `p ≥ 5`.

The strategy follows a reflection/oddness argument for an entire function `G`
on `ℤ_[p]` whose power-series coefficients are the sums `Σ s`.
-/

namespace PSigma

open PLog PKaz
open scoped Topology ENNReal NNReal
open FormalMultilinearSeries

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Step 1: the reflection product identity -/

/-- The block factor as a function of a `p`-adic integer variable `x`:
`∏_{i=1}^{p-1} (1 + x·p·i⁻¹)`. -/
noncomputable def oneAddWx (x : ℤ_[p]) : ℤ_[p] :=
  ∏ i ∈ Finset.Icc 1 (p - 1), (1 + x * (p : ℤ_[p]) * iv i)

/-- Each factor rewritten as `(i + x·p)·i⁻¹`. -/
lemma oneAddWx_eq (x : ℤ_[p]) :
    oneAddWx x
      = (∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℤ_[p]) + x * (p : ℤ_[p])))
        * (∏ i ∈ Finset.Icc 1 (p - 1), iv i) := by
  rw [oneAddWx, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hiv : (i : ℤ_[p]) * iv i = 1 := mul_iv_cancel hnd
  linear_combination (-1 : ℤ_[p]) * hiv

/-- The reflected product `∏ (i + (-1-x)p)` equals `∏ (i + xp)` (reindex `i ↦ p - i`,
using that `p - 1` is even). -/
lemma refl_prod (hp5 : 5 ≤ p) (x : ℤ_[p]) :
    ∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℤ_[p]) + (-1 - x) * (p : ℤ_[p]))
      = ∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℤ_[p]) + x * (p : ℤ_[p])) := by
  have hstep :
      ∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℤ_[p]) + (-1 - x) * (p : ℤ_[p]))
        = ∏ i ∈ Finset.Icc 1 (p - 1), (-((i : ℤ_[p]) + x * (p : ℤ_[p]))) := by
    refine Finset.prod_nbij' (fun i => p - i) (fun i => p - i) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      have hcast : ((p - a : ℕ) : ℤ_[p]) = (p : ℤ_[p]) - (a : ℤ_[p]) := by
        rw [Nat.cast_sub (by omega)]
      rw [hcast]; ring
  rw [hstep, Finset.prod_neg]
  have hcard : (Finset.Icc 1 (p - 1)).card = p - 1 := by rw [Nat.card_Icc]; omega
  rw [hcard]
  have heven : Even (p - 1) := by
    have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
    rcases hodd with ⟨m, hm⟩; exact ⟨m, by omega⟩
  rw [heven.neg_one_pow, one_mul]

/-- **Reflection identity:** `oneAddWx x = oneAddWx (-1 - x)`. -/
lemma oneAddWx_reflection (hp5 : 5 ≤ p) (x : ℤ_[p]) :
    oneAddWx x = oneAddWx (-1 - x) := by
  rw [oneAddWx_eq x, oneAddWx_eq (-1 - x), refl_prod hp5 x]

/-- Each factor `x·p·i⁻¹` has norm `< 1`. -/
lemma norm_wx_lt (hp5 : 5 ≤ p) (x : ℤ_[p]) (i : ℕ) :
    ‖x * (p : ℤ_[p]) * iv i‖ < 1 := by
  have h1 : ‖x * (p : ℤ_[p]) * iv i‖ ≤ ‖(p : ℤ_[p])‖ := by
    calc ‖x * (p : ℤ_[p]) * iv i‖ = ‖x‖ * ‖(p : ℤ_[p])‖ * ‖iv i‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖(p : ℤ_[p])‖ * 1 := by
          gcongr
          · exact PadicInt.norm_le_one x
          · exact PadicInt.norm_le_one _
      _ = ‖(p : ℤ_[p])‖ := by ring
  refine lt_of_le_of_lt h1 ?_
  rw [PadicInt.norm_p, inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
  exact_mod_cast (by omega : 1 < p)

lemma norm_oneAddWx_sub_one_lt (hp5 : 5 ≤ p) (x : ℤ_[p]) :
    ‖oneAddWx x - 1‖ < 1 := by
  rw [oneAddWx]
  exact norm_prod_one_add_sub_one_lt _ _ (fun i _ => norm_wx_lt hp5 x i)

/-- The function `g x = log(oneAddWx x - 1)`. -/
noncomputable def g (x : ℤ_[p]) : ℚ_[p] := padicLog (oneAddWx x - 1)

/-- **Reflection of `g`:** `g x = g (-1 - x)`. -/
lemma g_reflection (hp5 : 5 ≤ p) (x : ℤ_[p]) : g x = g (-1 - x) := by
  rw [g, g, oneAddWx_reflection hp5 x]

/-! ## Step 2: coefficients `a`, `d`, and the sums `Sig` -/

/-- The `k`-th coefficient of the power series `g`. -/
noncomputable def a (k : ℕ) : ℚ_[p] :=
  (-1) ^ (k - 1) * (p : ℚ_[p]) ^ k * ((Hz k : ℤ_[p]) : ℚ_[p]) / (k : ℚ_[p])

/-- The Faulhaber coefficient: coefficient of `N^s` in `∑_{t<N} t^k`. -/
noncomputable def d (k s : ℕ) : ℚ_[p] :=
  if s = 0 then 0
  else ((bernoulli (k + 1 - s) : ℚ) : ℚ_[p]) * ((Nat.choose (k + 1) s : ℕ) : ℚ_[p])
        / ((k + 1 : ℕ) : ℚ_[p])

lemma norm_a_le (k : ℕ) : ‖(a k : ℚ_[p])‖ ≤ (k : ℝ) * ((p : ℝ)⁻¹) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [a]
  · rw [a, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Padic.norm_p, PadicInt.padic_norm_e_of_padicInt, div_eq_mul_inv]
    calc ((p : ℝ)⁻¹) ^ k * ‖(Hz k : ℤ_[p])‖ * ‖(k : ℚ_[p])‖⁻¹
        ≤ ((p : ℝ)⁻¹) ^ k * 1 * (k : ℝ) := by
          gcongr
          · exact norm_Hz_le_one k
          · exact norm_natCast_inv_le k
      _ = (k : ℝ) * ((p : ℝ)⁻¹) ^ k := by ring

lemma norm_d_le (hp5 : 5 ≤ p) (k s : ℕ) : ‖(d k s : ℚ_[p])‖ ≤ (p : ℝ) * ((k : ℝ) + 1) := by
  rw [d]
  split_ifs with h
  · simp only [norm_zero]; positivity
  · rw [norm_div, norm_mul, div_eq_mul_inv]
    calc ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * ‖((Nat.choose (k + 1) s : ℕ) : ℚ_[p])‖
            * ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹
        ≤ (p : ℝ) * 1 * ((k : ℝ) + 1) := by
          gcongr
          · exact VonStaudt.norm_bernoulli_le hp5 _
          · exact VonStaudt.norm_nat_le_one _
          · calc ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹ ≤ ((k + 1 : ℕ) : ℝ) := norm_natCast_inv_le _
              _ = (k : ℝ) + 1 := by push_cast; ring
      _ = (p : ℝ) * ((k : ℝ) + 1) := by ring

lemma norm_ad_le (hp5 : 5 ≤ p) (k s : ℕ) :
    ‖(a k * d k s : ℚ_[p])‖ ≤ (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k := by
  rw [norm_mul]
  calc ‖a k‖ * ‖d k s‖
      ≤ ((k : ℝ) * ((p : ℝ)⁻¹) ^ k) * ((p : ℝ) * ((k : ℝ) + 1)) := by
        apply mul_le_mul (norm_a_le k) (norm_d_le hp5 k s) (norm_nonneg _) (by positivity)
    _ = (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k := by ring

lemma summable_cbound :
    Summable (fun k : ℕ => (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k) := by
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
    exact_mod_cast hp.out.one_lt
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have heq : (fun k : ℕ => (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k)
      = fun k : ℕ => (p : ℝ) * ((k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k)
          + (p : ℝ) * ((k : ℝ) ^ 1 * ((p : ℝ)⁻¹) ^ k) := by
    funext k; ring
  rw [heq]
  exact (h2.mul_left (p : ℝ)).add (h1.mul_left (p : ℝ))

lemma summable_ad (hp5 : 5 ≤ p) (s : ℕ) : Summable (fun k : ℕ => (a k * d k s : ℚ_[p])) :=
  Summable.of_norm_bounded summable_cbound (fun k => norm_ad_le hp5 k s)

/-- The `s`-th power-series coefficient of the summed function `G`. -/
noncomputable def Sig (s : ℕ) : ℚ_[p] := ∑' k, a k * d k s

lemma d_eq_zero_of_lt {k s : ℕ} (h : k + 1 < s) : d k s = (0 : ℚ_[p]) := by
  rw [d, if_neg (by omega : s ≠ 0), Nat.choose_eq_zero_of_lt h]
  simp

lemma Sig_zero : Sig (p := p) 0 = 0 := by
  rw [Sig]
  have : (fun k => a k * d k 0) = fun _ : ℕ => (0 : ℚ_[p]) := by
    funext k; rw [d, if_pos rfl, mul_zero]
  rw [this, tsum_zero]

/-- The uniform bound `p·k·(k+1)·p^{-k}`. -/
noncomputable def cbnd (p k : ℕ) : ℝ := (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k

lemma cbnd_nonneg (k : ℕ) : 0 ≤ cbnd p k := by rw [cbnd]; positivity

lemma norm_ad_le' (hp5 : 5 ≤ p) (k s : ℕ) : ‖(a k * d k s : ℚ_[p])‖ ≤ cbnd p k :=
  norm_ad_le hp5 k s

lemma cbnd_step (hp5 : 5 ≤ p) {k : ℕ} (hk : 1 ≤ k) : cbnd p (k + 1) ≤ cbnd p k := by
  have hr : (p : ℝ)⁻¹ ≤ 1 / 5 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp5)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set r := (p : ℝ)⁻¹ with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrk : 0 < r ^ k := by positivity
  have hkey : ((k : ℝ) + 2) * r ≤ (k : ℝ) := by
    have h1 : ((k : ℝ) + 2) * r ≤ ((k : ℝ) + 2) * (1 / 5) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    nlinarith [h1, hk1]
  rw [cbnd, cbnd, pow_succ]
  push_cast
  have hfac : 0 ≤ (p : ℝ) * ((k : ℝ) + 1) * r ^ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hkey hfac, hrk, hp0]

lemma cbnd_anti (hp5 : 5 ≤ p) : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → cbnd p n ≤ cbnd p m := by
  intro m n hm hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hmn ih => exact le_trans (cbnd_step hp5 (le_trans hm hmn)) ih

/-- Uniform-in-`k` bound giving `‖Sig s‖ ≤ cbnd (max 1 (s-1))`. -/
lemma norm_Sig_le (hp5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) :
    ‖Sig (p := p) s‖ ≤ cbnd p (max 1 (s - 1)) := by
  rw [Sig]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (cbnd_nonneg _) (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [a, Nat.zero_sub, pow_zero, Nat.cast_zero, one_mul, div_zero, zero_mul, mul_zero,
      norm_zero]
    exact cbnd_nonneg _
  · by_cases hks : k + 1 < s
    · rw [d_eq_zero_of_lt hks, mul_zero, norm_zero]; exact cbnd_nonneg _
    · refine le_trans (norm_ad_le' hp5 k s) ?_
      exact cbnd_anti hp5 (le_max_left _ _) (by omega)

lemma summable_Sig_norm_mul (hp5 : 5 ≤ p) :
    Summable (fun s : ℕ => ‖Sig (p := p) s‖ * (2 : ℝ) ^ s) := by
  apply Summable.comp_nat_add (k := 2)
  -- majorant M s = 4 (s+1)(s+2) (2/p)^s
  have hq : ‖((2 : ℝ) / p)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one (by exact_mod_cast hp.out.pos)]
    exact_mod_cast (by omega : 2 < p)
  have hM : Summable (fun s : ℕ => (4 : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) * ((2 : ℝ) / p) ^ s) := by
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
    have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hq
    have heq : (fun s : ℕ => (4 : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) * ((2 : ℝ) / p) ^ s)
        = fun s : ℕ => (4 : ℝ) * ((s : ℝ) ^ 2 * ((2 : ℝ) / p) ^ s)
            + ((12 : ℝ) * ((s : ℝ) ^ 1 * ((2 : ℝ) / p) ^ s)
              + (8 : ℝ) * ((s : ℝ) ^ 0 * ((2 : ℝ) / p) ^ s)) := by
      funext s; ring
    rw [heq]
    exact (h2.mul_left 4).add ((h1.mul_left 12).add (h0.mul_left 8))
  refine hM.of_nonneg_of_le (fun s => by positivity) (fun s => ?_)
  -- ‖Sig (s+2)‖ * 2^(s+2) ≤ 4 (s+1)(s+2) (2/p)^s
  have hb : ‖Sig (p := p) (s + 2)‖ ≤ cbnd p (s + 1) := by
    have := norm_Sig_le hp5 (s := s + 2) (by omega)
    simpa [show max 1 (s + 2 - 1) = s + 1 by omega] using this
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  calc ‖Sig (p := p) (s + 2)‖ * (2 : ℝ) ^ (s + 2)
      ≤ cbnd p (s + 1) * (2 : ℝ) ^ (s + 2) := by
        apply mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (4 : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) * ((2 : ℝ) / p) ^ s := by
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
        rw [cbnd]
        push_cast
        rw [show ((p : ℝ)⁻¹) ^ (s + 1) = ((p : ℝ) ^ (s + 1))⁻¹ from inv_pow _ _, div_pow]
        field_simp
        ring

lemma two_le_radius (hp5 : 5 ≤ p) : (2 : ℝ≥0∞) ≤ (ofScalars ℚ_[p] (Sig (p := p))).radius := by
  have hs : Summable (fun n => ‖(ofScalars ℚ_[p] (Sig (p := p))) n‖ * ((2 : ℝ≥0) : ℝ) ^ n) := by
    have := summable_Sig_norm_mul (p := p) hp5
    refine this.congr (fun n => ?_)
    rw [ofScalars_norm]; norm_num
  have := (ofScalars ℚ_[p] (Sig (p := p))).le_radius_of_summable_norm hs
  simpa using this

/-- The entire function `G x = ∑' s, Sig s · x^s`. -/
noncomputable def G : ℚ_[p] → ℚ_[p] := (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).sum

lemma G_eq (x : ℚ_[p]) : G x = ∑' s, Sig s * x ^ s := by
  rw [G, show (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).sum
      = FormalMultilinearSeries.ofScalarsSum Sig from rfl,
    FormalMultilinearSeries.ofScalars_sum_eq]
  exact tsum_congr (fun s => by rw [smul_eq_mul])

lemma radius_pos (hp5 : 5 ≤ p) : 0 < (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).radius :=
  lt_of_lt_of_le (by norm_num) (two_le_radius hp5)

lemma G_hasFPS (hp5 : 5 ≤ p) :
    HasFPowerSeriesOnBall (G (p := p)) (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))) 0
      (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).radius :=
  (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).hasFPowerSeriesOnBall (radius_pos hp5)

/-! ## Step 3: power series of `g` at naturals, Faulhaber, Fubini -/

lemma oneAddWx_natCast (t : ℕ) : oneAddWx (↑t : ℤ_[p]) = oneAddW t := by
  rw [oneAddWx, oneAddW]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [wfac]; push_cast; ring

/-- Summability of the `g`-power-series for any `x` in the closed unit ball. -/
lemma summable_apow (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) : Summable (fun k => a k * x ^ k) := by
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
    exact_mod_cast hp.out.one_lt
  apply Summable.of_norm_bounded (g := fun k : ℕ => (k : ℝ) * ((p : ℝ)⁻¹) ^ k)
  · have := summable_pow_mul_geometric_of_norm_lt_one 1 hr
    simpa using this
  · intro k
    rw [norm_mul, norm_pow]
    calc ‖a k‖ * ‖x‖ ^ k
        ≤ ‖a k‖ * 1 := by
          apply mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hx) (norm_nonneg _)
      _ = ‖a k‖ := mul_one _
      _ ≤ (k : ℝ) * ((p : ℝ)⁻¹) ^ k := norm_a_le k

/-- **Power series form of `g` at naturals:** `g t = ∑' k, a k · t^k`. -/
lemma g_series (hp5 : 5 ≤ p) (t : ℕ) :
    g (↑t : ℤ_[p]) = ∑' k, a k * ((t : ℚ_[p])) ^ k := by
  have hp3 : 3 ≤ p := by omega
  have hg : g (↑t : ℤ_[p]) = padicLog (oneAddW t - 1) := by rw [g, oneAddWx_natCast]
  have hlog : padicLog (oneAddW t - 1 : ℤ_[p])
      = ∑' n, ∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac t i) n := by
    rw [oneAddW, padicLog_prod hp3 _ _ (fun i _ => norm_wfac_lt hp5 t i),
      show (∑ i ∈ Finset.Icc 1 (p - 1), padicLog (wfac t i))
          = ∑ i ∈ Finset.Icc 1 (p - 1), ∑' n, logT (wfac t i) n from
        Finset.sum_congr rfl (fun i _ => padicLog_eq_logT _)]
    exact (Summable.tsum_finsetSum
      (fun i _ => summable_logT (wfac t i) (norm_wfac_lt hp5 t i))).symm
  have hterm : ∀ n : ℕ, (∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac t i) n)
      = a (n + 1) * ((t : ℚ_[p])) ^ (n + 1) := by
    intro n
    rw [term_val, a]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [hg, hlog, tsum_congr hterm,
    (summable_apow (t : ℚ_[p]) (VonStaudt.norm_nat_le_one t)).tsum_eq_zero_add]
  have h0 : a (0 : ℕ) * ((t : ℚ_[p])) ^ 0 = 0 := by simp [a]
  rw [h0, zero_add]

/-- **Faulhaber (cast to `ℚ_[p]`):** `∑_{t<n} t^k = ∑_{s<k+2} d k s · n^s`. -/
lemma faulhaber (n k : ℕ) :
    ∑ t ∈ Finset.range n, ((t : ℚ_[p])) ^ k
      = ∑ s ∈ Finset.range (k + 2), d k s * ((n : ℚ_[p])) ^ s := by
  have key := sum_range_pow n k
  have hL : (∑ t ∈ Finset.range n, ((t : ℚ_[p])) ^ k)
      = ((∑ t ∈ Finset.range n, ((t : ℚ)) ^ k : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_sum]; exact Finset.sum_congr rfl (fun t _ => by push_cast; ring)
  rw [hL, key, Rat.cast_sum,
    Finset.sum_range_succ' (fun s => d k s * ((n : ℚ_[p])) ^ s) (k + 1),
    show d k 0 * ((n : ℚ_[p])) ^ 0 = 0 from by rw [d, if_pos rfl, zero_mul], add_zero,
    ← Finset.sum_range_reflect (fun s => d k (s + 1) * ((n : ℚ_[p])) ^ (s + 1)) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [d, if_neg (by omega : (k + 1 - 1 - j) + 1 ≠ 0)]
  have e1 : (k + 1 - 1 - j) + 1 = k + 1 - j := by omega
  have e2 : k + 1 - ((k + 1 - 1 - j) + 1) = j := by omega
  have e3 : (k + 1).choose ((k + 1 - 1 - j) + 1) = (k + 1).choose j := by
    rw [e1, Nat.choose_symm (by omega : j ≤ k + 1)]
  rw [e2, e3, e1]
  push_cast
  ring

lemma summable_poly_geom (hp5 : 5 ≤ p) (j : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) ^ j * ((p : ℝ)⁻¹) ^ k) := by
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
    exact_mod_cast hp.out.one_lt
  exact summable_pow_mul_geometric_of_norm_lt_one j hr

/-- Summability over `ℕ × ℕ` of the double-indexed family used in the Fubini step. -/
lemma summable_F (hp5 : 5 ≤ p) (n : ℕ) :
    Summable (Function.uncurry (fun k s => a k * (d k s * ((n : ℚ_[p])) ^ s))) := by
  have hnn : ∀ ks : ℕ × ℕ, (0 : ℝ) ≤ if ks.2 < ks.1 + 2 then cbnd p ks.1 else 0 := by
    intro ks; split_ifs with h
    · exact cbnd_nonneg _
    · exact le_refl 0
  have hgsum : Summable (fun ks : ℕ × ℕ => if ks.2 < ks.1 + 2 then cbnd p ks.1 else 0) := by
    rw [summable_prod_of_nonneg hnn]
    refine ⟨fun k => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := Finset.range (k + 2))
        (fun s hs => by rw [Finset.mem_range] at hs; simp [if_neg (by omega : ¬ s < k + 2)])
    · have hinner : (fun k : ℕ => ∑' s, if s < k + 2 then cbnd p k else 0)
          = fun k : ℕ => ((k : ℝ) + 2) * cbnd p k := by
        funext k
        rw [tsum_eq_sum (s := Finset.range (k + 2))
          (fun s hs => by rw [Finset.mem_range] at hs; simp [if_neg (by omega : ¬ s < k + 2)])]
        have hcongr : ∑ s ∈ Finset.range (k + 2), (if s < k + 2 then cbnd p k else 0)
            = ∑ s ∈ Finset.range (k + 2), cbnd p k := by
          apply Finset.sum_congr rfl
          intro s hs; rw [Finset.mem_range] at hs; rw [if_pos hs]
        rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring
      rw [hinner]
      have h3 := summable_poly_geom hp5 3
      have h2 := summable_poly_geom hp5 2
      have h1 := summable_poly_geom hp5 1
      have heq : (fun k : ℕ => ((k : ℝ) + 2) * cbnd p k)
          = fun k : ℕ => (p : ℝ) * ((k : ℝ) ^ 3 * ((p : ℝ)⁻¹) ^ k)
              + ((3 * (p : ℝ)) * ((k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k)
                + (2 * (p : ℝ)) * ((k : ℝ) ^ 1 * ((p : ℝ)⁻¹) ^ k)) := by
        funext k; rw [cbnd]; ring
      rw [heq]
      exact (h3.mul_left _).add ((h2.mul_left _).add (h1.mul_left _))
  apply Summable.of_norm_bounded hgsum
  rintro ⟨k, s⟩
  change ‖a k * (d k s * ((n : ℚ_[p])) ^ s)‖ ≤ (if s < k + 2 then cbnd p k else 0)
  by_cases h : s < k + 2
  · rw [if_pos h, norm_mul, norm_mul, norm_pow]
    calc ‖a k‖ * (‖d k s‖ * ‖(n : ℚ_[p])‖ ^ s)
        ≤ ‖a k‖ * (‖d k s‖ * 1) := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) (VonStaudt.norm_nat_le_one n)
      _ = ‖a k * d k s‖ := by rw [mul_one, norm_mul]
      _ ≤ cbnd p k := norm_ad_le' hp5 k s
  · rw [if_neg h, d_eq_zero_of_lt (by omega), zero_mul, mul_zero, norm_zero]

/-- **Fubini identity:** `G n = ∑_{t<n} g t` on naturals. -/
lemma G_natCast (hp5 : 5 ≤ p) (n : ℕ) :
    G (↑n : ℚ_[p]) = ∑ t ∈ Finset.range n, g (↑t : ℤ_[p]) := by
  have hs0 : ∀ k, ∀ s ∉ Finset.range (k + 2),
      d k s * ((n : ℚ_[p])) ^ s = 0 := by
    intro k s hs; rw [Finset.mem_range] at hs
    rw [d_eq_zero_of_lt (by omega), zero_mul]
  have hswap : (∑ t ∈ Finset.range n, ∑' k, a k * ((t : ℚ_[p])) ^ k)
      = ∑' k, ∑ t ∈ Finset.range n, a k * ((t : ℚ_[p])) ^ k :=
    (Summable.tsum_finsetSum (fun t (_ : t ∈ Finset.range n) =>
      summable_apow (t : ℚ_[p]) (VonStaudt.norm_nat_le_one t))).symm
  have step1 : ∑ t ∈ Finset.range n, g (↑t : ℤ_[p])
      = ∑' k, ∑' s, a k * (d k s * ((n : ℚ_[p])) ^ s) := by
    rw [show (∑ t ∈ Finset.range n, g (↑t : ℤ_[p]))
        = ∑ t ∈ Finset.range n, ∑' k, a k * ((t : ℚ_[p])) ^ k from
      Finset.sum_congr rfl (fun t _ => g_series hp5 t), hswap]
    apply tsum_congr
    intro k
    rw [← Finset.mul_sum, faulhaber n k]
    rw [show (∑ s ∈ Finset.range (k + 2), d k s * ((n : ℚ_[p])) ^ s)
        = ∑' s, d k s * ((n : ℚ_[p])) ^ s from (tsum_eq_sum (hs0 k)).symm]
    rw [← tsum_mul_left]
  have hmarg₂ : ∀ s, Summable (fun k => a k * (d k s * ((n : ℚ_[p])) ^ s)) := by
    intro s
    have := (summable_ad hp5 s).mul_right ((n : ℚ_[p]) ^ s)
    exact this.congr (fun k => by ring)
  have hmarg₁ : ∀ k, Summable (fun s => a k * (d k s * ((n : ℚ_[p])) ^ s)) := by
    intro k
    refine summable_of_ne_finset_zero (s := Finset.range (k + 2)) (fun s hs => ?_)
    simp only [Finset.mem_range, not_lt] at hs
    rw [d_eq_zero_of_lt (by omega), zero_mul, mul_zero]
  rw [step1, ← Summable.tsum_comm' (summable_F hp5 n) hmarg₁ hmarg₂, G_eq]
  apply tsum_congr
  intro s
  rw [Sig, ← tsum_mul_right]
  exact tsum_congr (fun k => by ring)

/-- `G` is continuous on the image of `ℤ_[p]`. -/
lemma continuous_G_coe (hp5 : 5 ≤ p) :
    Continuous (fun z : ℤ_[p] => G (↑z : ℚ_[p])) := by
  have hcont := (G_hasFPS (p := p) hp5).continuousOn
  refine hcont.comp_continuous (by fun_prop) (fun z => ?_)
  have hz1 : ‖(↑z : ℚ_[p])‖ ≤ 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one z
  rw [EMetric.mem_ball, edist_zero_eq_enorm, ← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal ‖(↑z : ℚ_[p])‖ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hz1
    _ < 2 := by rw [ENNReal.ofReal_one]; norm_num
    _ ≤ _ := two_le_radius hp5

/-! ## Step 4: difference equation, oddness, and Σ₂ = 0 -/

/-- `G` composed with a map into the closed unit ball of `ℚ_[p]` is continuous. -/
lemma continuous_G_comp (hp5 : 5 ≤ p) {h : ℤ_[p] → ℚ_[p]} (hh : Continuous h)
    (hb : ∀ z, ‖h z‖ ≤ 1) : Continuous (fun z : ℤ_[p] => G (h z)) := by
  have hcont := (G_hasFPS (p := p) hp5).continuousOn
  refine hcont.comp_continuous hh (fun z => ?_)
  rw [EMetric.mem_ball, edist_zero_eq_enorm, ← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal ‖h z‖ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hb z)
    _ < 2 := by rw [ENNReal.ofReal_one]; norm_num
    _ ≤ _ := two_le_radius hp5

lemma G_zero (hp5 : 5 ≤ p) : G (0 : ℚ_[p]) = 0 := by
  have := G_natCast hp5 0
  simpa using this

lemma continuous_oneAddWx : Continuous (oneAddWx (p := p)) := by
  unfold oneAddWx
  exact continuous_finset_prod _ (fun i _ => by fun_prop)

lemma continuous_g (hp5 : 5 ≤ p) : Continuous (g (p := p)) := by
  have heq : (g (p := p)) = fun z : ℤ_[p] => Lfun p ((↑(oneAddWx z - 1) : ℚ_[p])) := by
    funext z; rw [g, padicLog_eq_Lfun _ (norm_oneAddWx_sub_one_lt hp5 z)]
  rw [heq]
  have hcont := (hasFPS_L (p := p)).continuousOn
  refine hcont.comp_continuous
    (continuous_subtype_val.comp (continuous_oneAddWx.sub continuous_const)) (fun z => ?_)
  have hz : ‖((↑(oneAddWx z - 1) : ℚ_[p]))‖ < 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact norm_oneAddWx_sub_one_lt hp5 z
  rw [EMetric.mem_ball, edist_zero_eq_enorm, ← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal ‖((↑(oneAddWx z - 1) : ℚ_[p]))‖
      < ENNReal.ofReal 1 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hz
    _ = 1 := ENNReal.ofReal_one
    _ ≤ _ := one_le_radius_cc

/-- **Difference equation:** `G(↑z + 1) - G(↑z) = g z` for all `z : ℤ_[p]`. -/
lemma diff_eq (hp5 : 5 ≤ p) (z : ℤ_[p]) :
    G ((↑z : ℚ_[p]) + 1) - G (↑z) = g z := by
  have hcF1 : Continuous (fun z : ℤ_[p] => G ((↑z : ℚ_[p]) + 1) - G (↑z)) := by
    refine Continuous.sub (continuous_G_comp hp5
      (continuous_subtype_val.add continuous_const) (fun z => ?_)) (continuous_G_coe hp5)
    have : (↑z : ℚ_[p]) + 1 = (↑(z + 1) : ℚ_[p]) := by push_cast; ring
    rw [this, PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one _
  have H : (fun z : ℤ_[p] => G ((↑z : ℚ_[p]) + 1) - G (↑z)) ∘ (Nat.cast : ℕ → ℤ_[p])
      = (g (p := p)) ∘ (Nat.cast : ℕ → ℤ_[p]) := by
    funext n
    simp only [Function.comp_apply]
    have hcast1 : (↑(↑n : ℤ_[p]) : ℚ_[p]) + 1 = (↑(n + 1) : ℚ_[p]) := by push_cast; ring
    have hcast2 : (↑(↑n : ℤ_[p]) : ℚ_[p]) = (↑n : ℚ_[p]) := by push_cast; ring
    rw [hcast1, hcast2, G_natCast hp5 (n + 1), G_natCast hp5 n, Finset.sum_range_succ]
    ring
  have hFeq := PadicInt.denseRange_natCast.equalizer hcF1 (continuous_g hp5) H
  exact congrFun hFeq z

/-- **Oddness of `G`:** `G(-↑z) = -G(↑z)`. -/
lemma G_odd (hp5 : 5 ≤ p) (z : ℤ_[p]) : G (-(↑z : ℚ_[p])) = -G (↑z) := by
  set Q : ℤ_[p] → ℚ_[p] := fun z => G (↑z) + G (-(↑z : ℚ_[p])) with hQ
  have Qstep : ∀ w : ℤ_[p], Q (w + 1) = Q w := by
    intro w
    have h1 := diff_eq hp5 w
    have h2 := diff_eq hp5 (-w - 1)
    have c1 : (↑(w + 1) : ℚ_[p]) = ↑w + 1 := by push_cast; ring
    have c2 : (-(↑(w + 1) : ℚ_[p])) = -↑w - 1 := by push_cast; ring
    have c3 : (↑(-w - 1) : ℚ_[p]) = -↑w - 1 := by push_cast; ring
    have c4 : (↑(-w - 1) : ℚ_[p]) + 1 = -↑w := by push_cast; ring
    have hg : g w = g (-w - 1) := by rw [g_reflection hp5 w]; congr 1; ring
    rw [c4, c3] at h2
    simp only [hQ]
    rw [c2, c1]
    linear_combination h1 - h2 + hg
  have hQ0 : Q 0 = 0 := by
    simp only [hQ]
    rw [show ((0 : ℤ_[p]) : ℚ_[p]) = 0 from by push_cast; ring, neg_zero, G_zero hp5]
    ring
  have hQnat : ∀ n : ℕ, Q (↑n) = 0 := by
    intro n
    induction n with
    | zero => simpa using hQ0
    | succ k ih =>
        have hc : (↑(k + 1) : ℤ_[p]) = (↑k) + 1 := by push_cast; ring
        rw [hc, Qstep, ih]
  have hneg_cont : Continuous (fun z : ℤ_[p] => -(↑z : ℚ_[p])) := continuous_subtype_val.neg
  have hneg_b : ∀ z : ℤ_[p], ‖-(↑z : ℚ_[p])‖ ≤ 1 := fun z => by
    rw [norm_neg, PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one z
  have hcQ : Continuous Q := by
    simp only [hQ]
    exact (continuous_G_coe hp5).add (continuous_G_comp hp5 hneg_cont hneg_b)
  have hQzero : Q = fun _ : ℤ_[p] => (0 : ℚ_[p]) :=
    PadicInt.denseRange_natCast.equalizer hcQ continuous_const (by funext n; simpa using hQnat n)
  have hz0 : Q z = 0 := congrFun hQzero z
  simp only [hQ] at hz0
  linear_combination hz0

/-- **Σ₂ = 0** in the form `Sig 2 = 0`. -/
lemma Sig_two_eq_zero (hp5 : 5 ≤ p) : Sig (p := p) 2 = 0 := by
  set P := FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p)) with hP
  have hG_at : HasFPowerSeriesAt (G (p := p)) P 0 := (G_hasFPS hp5).hasFPowerSeriesAt
  have hu0 : (-ContinuousLinearMap.id ℚ_[p] ℚ_[p]) (0 : ℚ_[p]) = 0 := by simp
  have hG_at' : HasFPowerSeriesAt (G (p := p)) P ((-ContinuousLinearMap.id ℚ_[p] ℚ_[p]) 0) := by
    rw [hu0]; exact hG_at
  have hGneg_at := hG_at'.compContinuousLinearMap (u := -ContinuousLinearMap.id ℚ_[p] ℚ_[p])
  rw [hP, FormalMultilinearSeries.ofScalars_comp_neg_id] at hGneg_at
  have hDadd := hG_at.add hGneg_at
  rw [hP, ← FormalMultilinearSeries.ofScalars_add] at hDadd
  have hD0 : (fun x : ℚ_[p] => G x + (G ∘ ⇑(-ContinuousLinearMap.id ℚ_[p] ℚ_[p])) x)
      =ᶠ[nhds 0] (0 : ℚ_[p] → ℚ_[p]) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℚ_[p]) one_pos] with x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hzc : (↑(⟨x, le_of_lt hx⟩ : ℤ_[p]) : ℚ_[p]) = x := rfl
    simp only [Function.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
      Pi.zero_apply]
    rw [← hzc, G_odd hp5 ⟨x, le_of_lt hx⟩]; ring
  have hzero := hDadd.eq_zero_of_eventually hD0
  have hc0 : (Sig (p := p) + fun k => (-1) ^ k * Sig k) = 0 :=
    (FormalMultilinearSeries.ofScalars_series_eq_zero ℚ_[p]).mp hzero
  have h2 := congrFun hc0 2
  simp only [Pi.add_apply, Pi.zero_apply] at h2
  rw [show ((-1 : ℚ_[p])) ^ 2 = 1 from by norm_num, one_mul] at h2
  have hmul : (2 : ℚ_[p]) * Sig 2 = 0 := by rw [two_mul]; exact h2
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- **Main theorem — Σ₂ = 0:** the second-order coefficient vanishes. -/
theorem sigma2_eq_zero (hp5 : 5 ≤ p) :
    HasSum (fun m : ℕ => (-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ (m + 1)
        * ((Hz (m + 1) : ℤ_[p]) : ℚ_[p]) * ((bernoulli m : ℚ) : ℚ_[p])) 0 := by
  have hSig : Sig (p := p) 2 = 0 := Sig_two_eq_zero hp5
  have hHS : HasSum (fun k : ℕ => (a k * d k 2 : ℚ_[p])) 0 := by
    have hsum := (summable_ad hp5 2).hasSum
    rw [← Sig] at hsum
    rwa [hSig] at hsum
  have hf0 : (a 0 * d 0 2 : ℚ_[p]) = 0 := by simp [a]
  have hshift : HasSum (fun m : ℕ => (a (m + 1) * d (m + 1) 2 : ℚ_[p])) 0 := by
    refine (hasSum_nat_add_iff (f := fun k : ℕ => (a k * d k 2 : ℚ_[p])) 1 (g := 0)).mpr ?_
    rw [Finset.sum_range_one, zero_add, hf0]
    exact hHS
  have hmul : HasSum (fun m : ℕ => (2 * (a (m + 1) * d (m + 1) 2) : ℚ_[p])) 0 := by
    have := hshift.mul_left 2; rwa [mul_zero] at this
  have hAeq : ∀ m : ℕ, (-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ (m + 1)
        * ((Hz (m + 1) : ℤ_[p]) : ℚ_[p]) * ((bernoulli m : ℚ) : ℚ_[p])
      = 2 * (a (m + 1) * d (m + 1) 2) := by
    intro m
    have e1 : (m + 1) - 1 = m := by omega
    have e2 : (m + 1) + 1 - 2 = m := by omega
    have hc : ((Nat.choose (m + 1 + 1) 2 : ℕ) : ℚ_[p]) = ((m : ℚ_[p]) + 2) * ((m : ℚ_[p]) + 1) / 2 := by
      rw [Nat.cast_choose_two]; push_cast; ring
    have hm1 : (m : ℚ_[p]) + 1 ≠ 0 := by
      rw [show (m : ℚ_[p]) + 1 = ((m + 1 : ℕ) : ℚ_[p]) from by push_cast; ring]
      exact_mod_cast Nat.succ_ne_zero m
    have hm2 : (m : ℚ_[p]) + 2 ≠ 0 := by
      rw [show (m : ℚ_[p]) + 2 = ((m + 2 : ℕ) : ℚ_[p]) from by push_cast; ring]
      exact_mod_cast Nat.succ_ne_zero (m + 1)
    have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
    rw [a, d, if_neg (by norm_num : (2 : ℕ) ≠ 0), e1, e2, hc,
      show ((m + 1 : ℕ) : ℚ_[p]) = (m : ℚ_[p]) + 1 from by push_cast; ring,
      show ((m + 1 + 1 : ℕ) : ℚ_[p]) = (m : ℚ_[p]) + 2 from by push_cast; ring]
    field_simp
  have hfun : (fun m : ℕ => (-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ (m + 1)
        * ((Hz (m + 1) : ℤ_[p]) : ℚ_[p]) * ((bernoulli m : ℚ) : ℚ_[p]))
      = (fun m : ℕ => 2 * (a (m + 1) * d (m + 1) 2)) := funext hAeq
  rw [hfun]
  exact hmul

/-- Corollary: the `tsum` version of `Σ₂ = 0`. -/
theorem sigma2_tsum (hp5 : 5 ≤ p) :
    ∑' m : ℕ, (-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ (m + 1)
        * ((Hz (m + 1) : ℤ_[p]) : ℚ_[p]) * ((bernoulli m : ℚ) : ℚ_[p]) = 0 :=
  (sigma2_eq_zero hp5).tsum_eq

end PSigma

end

section  -- ===== PStrong =====
namespace PStrong
open PLog PKaz PSigma
variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Part A: the sharp per-term bound `‖a k * d k s‖ ≤ p^{-3}` -/

/-- `v + 4 ≤ p^v` for `v ≥ 1`, `p ≥ 5`. -/
lemma pow_ge4 (hp5 : 5 ≤ p) : ∀ v : ℕ, 1 ≤ v → v + 4 ≤ p ^ v := by
  intro v
  induction v with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp only [zero_add, pow_one]; omega
    · have hih := ih hm
      have hps : p ^ (m + 1) = p * p ^ m := by rw [pow_succ, mul_comm]
      have hmul := Nat.mul_le_mul hp5 hih
      rw [← hps] at hmul
      omega

/-- `v + 5 ≤ p^v` for `v ≥ 2`, `p ≥ 5`. -/
lemma pow_ge5 (hp5 : 5 ≤ p) : ∀ v : ℕ, 2 ≤ v → v + 5 ≤ p ^ v := by
  intro v hv
  induction v, hv using Nat.le_induction with
  | base =>
      have h := Nat.mul_le_mul hp5 hp5
      rw [show (2 : ℕ) = 1 + 1 from rfl, pow_add, pow_one]
      omega
  | succ n hn ih =>
      have hps : p ^ (n + 1) = p * p ^ n := by rw [pow_succ, mul_comm]
      have hmul := Nat.mul_le_mul hp5 ih
      rw [← hps] at hmul
      omega

/-- At most one of `k`, `k+1` is divisible by `p`. -/
lemma valuation_coprime (hp5 : 5 ≤ p) (k : ℕ) :
    padicValNat p k = 0 ∨ padicValNat p (k + 1) = 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have hd1 : p ∣ k := (dvd_pow_self p h1).trans pow_padicValNat_dvd
  have hd2 : p ∣ (k + 1) := (dvd_pow_self p h2).trans pow_padicValNat_dvd
  have : p ∣ 1 := by
    have := Nat.dvd_sub hd2 hd1
    simpa using this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- The exponent bound: `3 + eB + v_p(k) + v_p(k+1) ≤ k`. -/
lemma exp_bound (hp5 : 5 ≤ p) {k : ℕ} (hk3 : 3 ≤ k) (eB : ℕ)
    (heB : eB = 0 ∨ (eB = 1 ∧ p ≤ k)) :
    3 + eB + padicValNat p k + padicValNat p (k + 1) ≤ k := by
  have hvk : p ^ (padicValNat p k) ≤ k := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have hvk1 : p ^ (padicValNat p (k + 1)) ≤ k + 1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have hcop := valuation_coprime hp5 k
  set vk := padicValNat p k with hvkdef
  set vk1 := padicValNat p (k + 1) with hvk1def
  have Lk : vk = 0 ∨ vk + 4 ≤ k := by
    rcases Nat.eq_zero_or_pos vk with h | h
    · left; exact h
    · right; exact le_trans (pow_ge4 hp5 vk h) hvk
  have Lk1 : vk1 = 0 ∨ vk1 + 4 ≤ k + 1 := by
    rcases Nat.eq_zero_or_pos vk1 with h | h
    · left; exact h
    · right; exact le_trans (pow_ge4 hp5 vk1 h) hvk1
  have Lk1' : vk1 = 0 ∨ vk1 = 1 ∨ vk1 + 5 ≤ k + 1 := by
    rcases Nat.eq_zero_or_pos vk1 with h | h
    · left; exact h
    · rcases Nat.lt_or_ge vk1 2 with h2 | h2
      · right; left; omega
      · right; right; exact le_trans (pow_ge5 hp5 vk1 h2) hvk1
  omega

/-- `((p:ℝ)⁻¹)^n = (p:ℝ)^(-(n:ℤ))`. -/
lemma rpow_neg (n : ℕ) : ((p : ℝ)⁻¹) ^ n = (p : ℝ) ^ (-(n : ℤ)) := by
  rw [inv_pow, ← zpow_natCast (p : ℝ) n, ← zpow_neg]

/-- `‖(k:ℚ_[p])‖⁻¹ = p^{v_p(k)}` for `k ≠ 0`. -/
lemma norm_natCast_inv_eq {k : ℕ} (hk : k ≠ 0) :
    ‖(k : ℚ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p k : ℤ) := by
  rw [VonStaudt.norm_natCast_eq k hk, ← zpow_neg, neg_neg]

/-- `‖(n:ℚ_[p])‖ = 1` when `p ∤ n`. -/
lemma norm_natCast_eq_one {n : ℕ} (hn : ¬ p ∣ n) : ‖(n : ℚ_[p])‖ = 1 := by
  rw [← PadicInt.coe_natCast, PadicInt.padic_norm_e_of_padicInt, PKaz.norm_cast_eq_one hn]

/-- Exact norm of `a k`. -/
lemma norm_a_eq (k : ℕ) :
    ‖(PSigma.a k : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ k * ‖(Hz k : ℤ_[p])‖ * ‖(k : ℚ_[p])‖⁻¹ := by
  rw [PSigma.a, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Padic.norm_p, PadicInt.padic_norm_e_of_padicInt, div_eq_mul_inv]

/-- Bound on `‖d k s‖`. -/
lemma norm_d_le3 (k s : ℕ) (hs : 1 ≤ s) :
    ‖(d k s : ℚ_[p])‖ ≤ ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * (p : ℝ) ^ (padicValNat p (k + 1) : ℤ) := by
  rw [d, if_neg (by omega : s ≠ 0), norm_div, norm_mul, div_eq_mul_inv,
    norm_natCast_inv_eq (by omega : k + 1 ≠ 0)]
  calc ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * ‖((Nat.choose (k + 1) s : ℕ) : ℚ_[p])‖
          * (p : ℝ) ^ (padicValNat p (k + 1) : ℤ)
      ≤ ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * 1 * (p : ℝ) ^ (padicValNat p (k + 1) : ℤ) := by
        gcongr
        exact VonStaudt.norm_nat_le_one _
    _ = ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * (p : ℝ) ^ (padicValNat p (k + 1) : ℤ) := by ring

/-- `‖a 1‖ ≤ p^{-3}`. -/
lemma norm_a_one_le (hp5 : 5 ≤ p) : ‖(PSigma.a (1 : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [norm_a_eq]
  have h1 : ‖((1 : ℕ) : ℚ_[p])‖⁻¹ = 1 := by simp
  rw [h1, mul_one, pow_one, show (p : ℝ)⁻¹ = (p : ℝ) ^ (-(1 : ℕ) : ℤ) by
    rw [← rpow_neg 1, pow_one]]
  calc (p : ℝ) ^ (-(1 : ℕ) : ℤ) * ‖(Hz 1 : ℤ_[p])‖
      ≤ (p : ℝ) ^ (-(1 : ℕ) : ℤ) * (p : ℝ) ^ (-2 : ℤ) := by
        gcongr
        exact norm_Hz_one_le hp5
    _ = (p : ℝ) ^ (-3 : ℤ) := by
        rw [← zpow_add₀ (ne_of_gt hp0)]; congr 1

/-- `‖a 2‖ ≤ p^{-3}`. -/
lemma norm_a_two_le (hp5 : 5 ≤ p) : ‖(PSigma.a (2 : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  rw [norm_a_eq]
  have h1 : ‖((2 : ℕ) : ℚ_[p])‖⁻¹ = 1 := by
    rw [inv_eq_one]; exact norm_natCast_eq_one hnd2
  rw [h1, mul_one, rpow_neg 2]
  calc (p : ℝ) ^ (-(2 : ℕ) : ℤ) * ‖(Hz 2 : ℤ_[p])‖
      ≤ (p : ℝ) ^ (-(2 : ℕ) : ℤ) * (p : ℝ) ^ (-1 : ℤ) := by
        gcongr
        exact norm_Hz_two_le hp5
    _ = (p : ℝ) ^ (-3 : ℤ) := by
        rw [← zpow_add₀ (ne_of_gt hp0)]; congr 1

/-- The sharp per-term bound. -/
lemma norm_ad_le3 (hp5 : 5 ≤ p) (k s : ℕ) (hk : 1 ≤ k) (hs : 2 ≤ s) :
    ‖(PSigma.a k * d k s : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp0ne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  by_cases hks : k + 1 < s
  · rw [d_eq_zero_of_lt hks, mul_zero, norm_zero]; positivity
  push_neg at hks
  rw [norm_mul]
  have hnd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hnd3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  by_cases hk1 : k = 1
  · -- k = 1, s = 2
    subst hk1
    have hs2 : s = 2 := by omega
    subst hs2
    have hd1 : ‖(d 1 2 : ℚ_[p])‖ ≤ 1 := by
      refine le_trans (norm_d_le3 1 2 (by norm_num)) ?_
      have he : (1 : ℕ) + 1 - 2 = 0 := by norm_num
      have hv2 : padicValNat p (1 + 1) = 0 :=
        padicValNat.eq_zero_of_not_dvd (by simpa using hnd2)
      rw [he, bernoulli_zero, hv2]
      simp
    calc ‖(PSigma.a 1 : ℚ_[p])‖ * ‖(d 1 2 : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) * 1 :=
          mul_le_mul (norm_a_one_le hp5) hd1 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (-3 : ℤ) := mul_one _
  by_cases hk2 : k = 2
  · -- k = 2, s ∈ {2, 3}
    subst hk2
    have hd2 : ‖(d 2 s : ℚ_[p])‖ ≤ 1 := by
      refine le_trans (norm_d_le3 2 s (by omega)) ?_
      have hv3 : padicValNat p (2 + 1) = 0 :=
        padicValNat.eq_zero_of_not_dvd (by simpa using hnd3)
      rw [hv3, Nat.cast_zero, zpow_zero, mul_one]
      interval_cases s
      · have he : (2 : ℕ) + 1 - 2 = 1 := by norm_num
        rw [he]
        refine VonStaudt.norm_bernoulli_le_one_of_not_dvd hp5 1 ?_
        intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
      · have he : (2 : ℕ) + 1 - 3 = 0 := by norm_num
        rw [he, bernoulli_zero]; simp
    calc ‖(PSigma.a 2 : ℚ_[p])‖ * ‖(d 2 s : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) * 1 :=
          mul_le_mul (norm_a_two_le hp5) hd2 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (-3 : ℤ) := mul_one _
  -- k ≥ 3
  have hk3 : 3 ≤ k := by omega
  have ha3 : ‖(PSigma.a k : ℚ_[p])‖ ≤ (p : ℝ) ^ ((padicValNat p k : ℤ) - k) := by
    rw [norm_a_eq, norm_natCast_inv_eq (by omega : k ≠ 0), rpow_neg k]
    calc (p : ℝ) ^ (-(k : ℤ)) * ‖(Hz k : ℤ_[p])‖ * (p : ℝ) ^ (padicValNat p k : ℤ)
        ≤ (p : ℝ) ^ (-(k : ℤ)) * 1 * (p : ℝ) ^ (padicValNat p k : ℤ) := by
          gcongr
          exact norm_Hz_le_one k
      _ = (p : ℝ) ^ ((padicValNat p k : ℤ) - k) := by
          rw [mul_one, ← zpow_add₀ hp0ne]; congr 1; ring
  set m := k + 1 - s with hm
  by_cases hbc : (p - 1) ∣ m ∧ 2 ≤ m
  · -- bernoulli factor ≤ p, and p ≤ k
    have hbern : ‖((bernoulli m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (1 : ℤ) := by
      rw [zpow_one]; exact VonStaudt.norm_bernoulli_le hp5 m
    have hd3 : ‖(d k s : ℚ_[p])‖ ≤ (p : ℝ) ^ ((1 : ℤ) + padicValNat p (k + 1)) := by
      refine le_trans (norm_d_le3 k s (by omega)) ?_
      rw [← hm, zpow_add₀ hp0ne]
      exact mul_le_mul_of_nonneg_right hbern (by positivity)
    have hmpos : 0 < m := by omega
    have hge : p - 1 ≤ m := Nat.le_of_dvd hmpos hbc.1
    have hpk : p ≤ k := by omega
    calc ‖(PSigma.a k : ℚ_[p])‖ * ‖d k s‖
        ≤ (p : ℝ) ^ ((padicValNat p k : ℤ) - k)
            * (p : ℝ) ^ ((1 : ℤ) + padicValNat p (k + 1)) :=
          mul_le_mul ha3 hd3 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (((padicValNat p k : ℤ) - k) + ((1 : ℤ) + padicValNat p (k + 1))) := by
          rw [← zpow_add₀ hp0ne]
      _ ≤ (p : ℝ) ^ (-3 : ℤ) := by
          apply zpow_le_zpow_right₀ hp1
          have := exp_bound hp5 hk3 1 (Or.inr ⟨rfl, hpk⟩)
          omega
  · -- bernoulli factor ≤ 1
    have hbern : ‖((bernoulli m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (0 : ℤ) := by
      rw [zpow_zero]
      by_cases hd : (p - 1) ∣ m
      · have hm0 : m = 0 := by
          rcases Nat.lt_or_ge m 2 with h2 | h2
          · interval_cases m
            · rfl
            · exact absurd hd (fun hdd => by have := Nat.le_of_dvd (by norm_num) hdd; omega)
          · exact absurd ⟨hd, h2⟩ hbc
        rw [hm0, bernoulli_zero]; simp
      · exact VonStaudt.norm_bernoulli_le_one_of_not_dvd hp5 m hd
    have hd3 : ‖(d k s : ℚ_[p])‖ ≤ (p : ℝ) ^ ((0 : ℤ) + padicValNat p (k + 1)) := by
      refine le_trans (norm_d_le3 k s (by omega)) ?_
      rw [← hm, zpow_add₀ hp0ne]
      exact mul_le_mul_of_nonneg_right hbern (by positivity)
    calc ‖(PSigma.a k : ℚ_[p])‖ * ‖d k s‖
        ≤ (p : ℝ) ^ ((padicValNat p k : ℤ) - k)
            * (p : ℝ) ^ ((0 : ℤ) + padicValNat p (k + 1)) :=
          mul_le_mul ha3 hd3 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (((padicValNat p k : ℤ) - k) + ((0 : ℤ) + padicValNat p (k + 1))) := by
          rw [← zpow_add₀ hp0ne]
      _ ≤ (p : ℝ) ^ (-3 : ℤ) := by
          apply zpow_le_zpow_right₀ hp1
          have := exp_bound hp5 hk3 0 (Or.inl rfl)
          omega

/-- The sharp bound on `‖Sig s‖` for `s ≥ 2`. -/
lemma norm_Sig_le3 (hp5 : 5 ≤ p) (s : ℕ) (hs : 2 ≤ s) :
    ‖Sig (p := p) s‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  rw [Sig]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [PSigma.a, Nat.zero_sub, pow_zero, Nat.cast_zero, one_mul, div_zero, zero_mul, mul_zero,
      norm_zero]
    positivity
  · exact norm_ad_le3 hp5 k s hk hs

/-! ## Part B: the log-difference bound `‖L‖ ≤ p^{-3r}` -/

/-- `∑' t ‖Sig t‖` is summable. -/
lemma summable_Sig_norm (hp5 : 5 ≤ p) : Summable (fun t : ℕ => ‖Sig (p := p) t‖) := by
  refine Summable.of_nonneg_of_le (fun t => norm_nonneg _) (fun t => ?_) (summable_Sig_norm_mul hp5)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ t := one_le_pow₀ (by norm_num)
  calc ‖Sig (p := p) t‖ = ‖Sig (p := p) t‖ * 1 := (mul_one _).symm
    _ ≤ ‖Sig (p := p) t‖ * (2 : ℝ) ^ t := by gcongr

/-- `Summable (fun t => Sig t * x^t)` for `‖x‖ ≤ 1`. -/
lemma summable_Sig_mul_pow (hp5 : 5 ≤ p) (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) :
    Summable (fun t : ℕ => Sig (p := p) t * x ^ t) := by
  refine Summable.of_norm_bounded (summable_Sig_norm hp5) (fun t => ?_)
  rw [norm_mul, norm_pow]
  calc ‖Sig (p := p) t‖ * ‖x‖ ^ t ≤ ‖Sig (p := p) t‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hx
    _ = ‖Sig (p := p) t‖ := mul_one _

/-- The norm of a finite sum of `t`-th powers of naturals is `≤ 1`. -/
lemma norm_sum_pow_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (t : ℕ) :
    ‖∑ i ∈ s, ((f i : ℚ_[p])) ^ t‖ ≤ 1 := by
  rw [show (∑ i ∈ s, ((f i : ℚ_[p])) ^ t) = ((∑ i ∈ s, (f i) ^ t : ℕ) : ℚ_[p]) by push_cast; ring]
  exact VonStaudt.norm_nat_le_one _

/-- `g (↑j) = padicLog (w j)`. -/
lemma g_eq_padicLog_w (j : ℕ) : g (↑j : ℤ_[p]) = padicLog (w (p := p) j) := by
  rw [g, oneAddWx_natCast]; rfl

/-- `padicLog (Aprod s cnt - 1) = ∑ i ∈ s, G (↑(cnt i))`. -/
lemma padicLog_Aprod_eq_sum_G (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    padicLog (Aprod (p := p) s cnt - 1) = ∑ i ∈ s, G (↑(cnt i) : ℚ_[p]) := by
  rw [padicLog_Aprod hp5, Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [G_natCast hp5]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (g_eq_padicLog_w j).symm

/-- `padicLog (Aprod s cnt - 1) = ∑' t, Sig t * (∑ i ∈ s, (cnt i)^t)`. -/
lemma padicLog_Aprod_tsum (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    padicLog (Aprod (p := p) s cnt - 1)
      = ∑' t : ℕ, Sig (p := p) t * (∑ i ∈ s, ((cnt i : ℚ_[p])) ^ t) := by
  rw [padicLog_Aprod_eq_sum_G hp5,
    show (∑ i ∈ s, G (↑(cnt i) : ℚ_[p]))
        = ∑ i ∈ s, ∑' t : ℕ, Sig (p := p) t * ((cnt i : ℚ_[p])) ^ t from
      Finset.sum_congr rfl (fun i _ => G_eq _),
    ← Summable.tsum_finsetSum
      (fun i (_ : i ∈ s) => summable_Sig_mul_pow hp5 _ (VonStaudt.norm_nat_le_one _))]
  exact tsum_congr (fun t => by rw [Finset.mul_sum])

/-- The log-difference bound. -/
lemma logdiff_le (hp5 : 5 ≤ p) {ι : Type*} (num den : Finset ι) (c : ι → ℕ)
    (n r : ℕ) (hnp : ¬ p ∣ n) (hr : 1 ≤ r)
    (hbal : ∑ i ∈ num, c i = ∑ i ∈ den, c i) :
    ‖padicLog (Aprod (p := p) num (fun i => c i * (n * p ^ (r - 1))) - 1)
        - padicLog (Aprod (p := p) den (fun i => c i * (n * p ^ (r - 1))) - 1)‖
      ≤ (p : ℝ) ^ (-((3 * r : ℕ) : ℤ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hinv_le_one : (p : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; exact hp1
  set M' := n * p ^ (r - 1) with hM'
  -- norm of M'
  have hM'norm : ‖((M' : ℕ) : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ (r - 1) := by
    rw [hM']; push_cast
    rw [norm_mul, norm_pow, norm_natCast_eq_one hnp, one_mul, Padic.norm_p]
  have hM1 : ‖((M' : ℕ) : ℚ_[p])‖ ≤ 1 := by
    rw [hM'norm]; exact pow_le_one₀ (by positivity) hinv_le_one
  -- expand both logs
  have key : ∀ s : Finset ι,
      padicLog (Aprod (p := p) s (fun i => c i * M') - 1)
        = ∑' t : ℕ, Sig (p := p) t
            * ((M' : ℚ_[p]) ^ t * (∑ i ∈ s, ((c i : ℚ_[p])) ^ t)) := by
    intro s
    rw [padicLog_Aprod_tsum hp5]
    refine tsum_congr (fun t => ?_)
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast; ring
  -- summability of the two tsum families
  have hsummand : ∀ (s : Finset ι) (t : ℕ),
      ‖Sig (p := p) t * ((M' : ℚ_[p]) ^ t * (∑ i ∈ s, ((c i : ℚ_[p])) ^ t))‖
        ≤ ‖Sig (p := p) t‖ := by
    intro s t
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖Sig (p := p) t‖ * (‖((M' : ℕ) : ℚ_[p])‖ ^ t * ‖∑ i ∈ s, ((c i : ℚ_[p])) ^ t‖)
        ≤ ‖Sig (p := p) t‖ * (1 * 1) := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) hM1
          · exact norm_sum_pow_le s c t
      _ = ‖Sig (p := p) t‖ := by ring
  have hsA : Summable (fun t : ℕ =>
      Sig (p := p) t * ((M' : ℚ_[p]) ^ t * (∑ i ∈ num, ((c i : ℚ_[p])) ^ t))) :=
    Summable.of_norm_bounded (summable_Sig_norm hp5) (fun t => hsummand num t)
  have hsB : Summable (fun t : ℕ =>
      Sig (p := p) t * ((M' : ℚ_[p]) ^ t * (∑ i ∈ den, ((c i : ℚ_[p])) ^ t))) :=
    Summable.of_norm_bounded (summable_Sig_norm hp5) (fun t => hsummand den t)
  rw [key num, key den, ← Summable.tsum_sub hsA hsB]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) (fun t => ?_)
  rcases t with _ | _ | _ | u
  · -- t = 0
    rw [Sig_zero]
    simp only [zero_mul, sub_zero, norm_zero]
    positivity
  · -- t = 1
    have h1 : (∑ i ∈ num, ((c i : ℚ_[p])) ^ 1) = ∑ i ∈ den, ((c i : ℚ_[p])) ^ 1 := by
      simp only [pow_one]
      have en : (∑ i ∈ num, (c i : ℚ_[p])) = ((∑ i ∈ num, c i : ℕ) : ℚ_[p]) := by push_cast; ring
      have ed : (∑ i ∈ den, (c i : ℚ_[p])) = ((∑ i ∈ den, c i : ℕ) : ℚ_[p]) := by push_cast; ring
      rw [en, ed, hbal]
    rw [h1, sub_self, norm_zero]; positivity
  · -- t = 2
    rw [Sig_two_eq_zero hp5]
    simp only [zero_mul, sub_zero, norm_zero]
    positivity
  · -- t = u + 3
    have hfac :
        Sig (p := p) (u + 3) * ((M' : ℚ_[p]) ^ (u + 3) * ∑ i ∈ num, ((c i : ℚ_[p])) ^ (u + 3))
          - Sig (p := p) (u + 3) * ((M' : ℚ_[p]) ^ (u + 3) * ∑ i ∈ den, ((c i : ℚ_[p])) ^ (u + 3))
        = Sig (p := p) (u + 3) * (M' : ℚ_[p]) ^ (u + 3)
            * ((∑ i ∈ num, ((c i : ℚ_[p])) ^ (u + 3)) - (∑ i ∈ den, ((c i : ℚ_[p])) ^ (u + 3))) := by
      ring
    rw [hfac, norm_mul, norm_mul, norm_pow, hM'norm]
    have hSig : ‖Sig (p := p) (u + 3)‖ ≤ ((p : ℝ)⁻¹) ^ 3 := by
      have hz3 : ((p : ℝ)⁻¹) ^ 3 = (p : ℝ) ^ (-3 : ℤ) := by rw [rpow_neg]; norm_num
      rw [hz3]; exact norm_Sig_le3 hp5 (u + 3) (by omega)
    have hdiff : ‖(∑ i ∈ num, ((c i : ℚ_[p])) ^ (u + 3))
        - (∑ i ∈ den, ((c i : ℚ_[p])) ^ (u + 3))‖ ≤ 1 := by
      rw [sub_eq_add_neg]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [norm_neg]
      exact max_le (norm_sum_pow_le num c (u + 3)) (norm_sum_pow_le den c (u + 3))
    calc ‖Sig (p := p) (u + 3)‖ * (((p : ℝ)⁻¹) ^ (r - 1)) ^ (u + 3)
            * ‖(∑ i ∈ num, ((c i : ℚ_[p])) ^ (u + 3))
                - (∑ i ∈ den, ((c i : ℚ_[p])) ^ (u + 3))‖
        ≤ ((p : ℝ)⁻¹) ^ 3 * (((p : ℝ)⁻¹) ^ (r - 1)) ^ (u + 3) * 1 := by
          gcongr
      _ = ((p : ℝ)⁻¹) ^ (3 + (r - 1) * (u + 3)) := by rw [mul_one, ← pow_mul, ← pow_add]
      _ ≤ ((p : ℝ)⁻¹) ^ (3 * r) := by
          apply pow_le_pow_of_le_one (by positivity) hinv_le_one
          have hle : (r - 1) * 3 ≤ (r - 1) * (u + 3) :=
            Nat.mul_le_mul (le_refl (r - 1)) (by omega)
          omega
      _ = (p : ℝ) ^ (-((3 * r : ℕ) : ℤ)) := rpow_neg (3 * r)

/-! ## Part C: divisibility from a log-difference bound -/

/-- If `u, v` are close to `1` and their log-difference is divisible by `p^V`, then `p^V ∣ u - v`. -/
lemma dvd_sub_of_logdiff (hp5 : 5 ≤ p) (u v : ℤ_[p])
    (hu : ‖u - 1‖ < 1) (hv : ‖v - 1‖ < 1) (V : ℕ)
    (hL : ‖padicLog (u - 1) - padicLog (v - 1)‖ ≤ (p : ℝ) ^ (-(V : ℤ))) :
    (p : ℤ_[p]) ^ V ∣ (u - v) := by
  have hp3 : 3 ≤ p := by omega
  have hvnorm : ‖v‖ = 1 := by
    have : ‖v‖ = ‖(v - 1) + 1‖ := by ring_nf
    rw [this]
    have h1 : ‖((1 : ℤ_[p]))‖ = 1 := norm_one
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := v - 1) (y := (1 : ℤ_[p])) (by rw [h1]; exact ne_of_lt hv)
    rw [this, h1]; exact max_eq_right (le_of_lt hv)
  set vinv : ℤ_[p] := PadicInt.inv v with hvinv
  have hvvinv : v * vinv = 1 := PadicInt.mul_inv hvnorm
  set r : ℤ_[p] := u * vinv with hr
  have hrsub : r - 1 = (u - v) * vinv := by
    rw [hr]
    have : u * vinv - 1 = u * vinv - v * vinv := by rw [hvvinv]
    rw [this]; ring
  have hvinv_norm : ‖vinv‖ = 1 := by
    have := congrArg norm hvvinv
    rw [norm_mul, hvnorm, one_mul, norm_one] at this; exact this
  have huvnorm : ‖u - v‖ < 1 := by
    calc ‖u - v‖ = ‖(u - 1) - (v - 1)‖ := by ring_nf
      _ ≤ max ‖u - 1‖ ‖v - 1‖ := norm_sub_le_max' _ _
      _ < 1 := max_lt hu hv
  have hrsubnorm : ‖r - 1‖ < 1 := by
    rw [hrsub, norm_mul, hvinv_norm, mul_one]; exact huvnorm
  have hrv : r * v = u := by rw [hr]; rw [mul_assoc, mul_comm vinv v, hvvinv, mul_one]
  have hmul := padicLog_mul hp3 (r - 1) (v - 1) hrsubnorm hv
  have hexp : (r - 1) + (v - 1) + (r - 1) * (v - 1) = r * v - 1 := by ring
  rw [hexp, hrv] at hmul
  have hlogr : padicLog (r - 1) = padicLog (u - 1) - padicLog (v - 1) := by rw [hmul]; ring
  have hlogr_le : ‖padicLog (r - 1)‖ ≤ (p : ℝ) ^ (-(V : ℤ)) := by rw [hlogr]; exact hL
  have hdvd : (p : ℤ_[p]) ^ V ∣ (r - 1) :=
    sub_one_dvd_of_padicLog hp3 r hrsubnorm V hlogr_le
  have huv : u - v = (r - 1) * v := by
    rw [hrsub, mul_assoc]
    rw [show vinv * v = 1 from by rw [mul_comm]; exact hvvinv, mul_one]
  rw [huv]; exact hdvd.mul_right v

/-! ## The strong supercongruence mod `p^{3r}` -/

/-- **Strong balanced supercongruence (mod `p^{3r}`).** -/
theorem strong_supercongruence (hp5 : 5 ≤ p) {ι : Type*}
    (num den : Finset ι) (c : ι → ℕ) (n r : ℕ) (hnp : ¬ p ∣ n) (hr : 1 ≤ r)
    (hbal : ∑ i ∈ num, c i = ∑ i ∈ den, c i) :
    (p : ℤ_[p]) ^ (3 * r) ∣
      ((∏ i ∈ num, Wfac (c i * (n * p ^ r))) - (∏ i ∈ den, Wfac (c i * (n * p ^ r)))) := by
  have hWeq : n * p ^ r = p * (n * p ^ (r - 1)) := by
    have hpr : p ^ r = p * p ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) from by omega]
      rw [pow_add, pow_one]
    rw [hpr]; ring
  rw [Wprod_eq (n * p ^ r) (n * p ^ (r - 1)) hWeq num c,
      Wprod_eq (n * p ^ r) (n * p ^ (r - 1)) hWeq den c]
  have hexp : (∑ i ∈ num, c i * (n * p ^ (r - 1))) = (∑ i ∈ den, c i * (n * p ^ (r - 1))) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hbal]
  rw [hexp, ← mul_sub]
  have hdvd : (p : ℤ_[p]) ^ (3 * r) ∣
      (Aprod (p := p) num (fun i => c i * (n * p ^ (r - 1)))
        - Aprod (p := p) den (fun i => c i * (n * p ^ (r - 1)))) := by
    refine dvd_sub_of_logdiff hp5 _ _
      (norm_Aprod_sub_one_lt hp5 num _) (norm_Aprod_sub_one_lt hp5 den _) (3 * r) ?_
    exact logdiff_le hp5 num den c n r hnp hr hbal
  exact hdvd.mul_left _

end PStrong

end

section  -- ===== PBridge =====

open scoped Real


namespace PBridge

open PLog PKaz PSigma PStrong

variable {p : ℕ} [Fact p.Prime]

lemma prod_Icc_eq_fact (n : ℕ) : ∏ j ∈ Finset.Icc 1 n, j = n.factorial := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; ring

/-- Natural-number version of `Wfac`: `∏_{1 ≤ j ≤ m, p ∤ j} j`. -/
def WfacN (m : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 m).filter (fun j => ¬ p ∣ j), j

lemma WfacN_cast (m : ℕ) : ((WfacN (p := p) m : ℕ) : ℤ_[p]) = Wfac m := by
  rw [WfacN, Wfac, Nat.cast_prod]

/-- The block decomposition of a factorial: `(pL)! = WfacN(pL) · p^L · L!`. -/
lemma factorial_block (L : ℕ) :
    (p * L).factorial = WfacN (p := p) (p * L) * p ^ L * L.factorial := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  -- `(pL)! = ∏_{j ∈ Icc 1 (pL)} j`
  have hfac : (p * L).factorial = ∏ j ∈ Finset.Icc 1 (p * L), j :=
    (prod_Icc_eq_fact (p * L)).symm
  -- split the product by divisibility by `p`
  have hsplit : (∏ j ∈ Finset.Icc 1 (p * L), j)
      = (∏ j ∈ (Finset.Icc 1 (p * L)).filter (fun j => ¬ p ∣ j), j)
        * (∏ j ∈ (Finset.Icc 1 (p * L)).filter (fun j => p ∣ j), j) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * L)) (fun j => p ∣ j)
        (fun j => j), mul_comm]
  -- the `p ∣ j` part is `∏_{k ∈ Icc 1 L} (p k) = p^L · L!`
  have hdvd : (∏ j ∈ (Finset.Icc 1 (p * L)).filter (fun j => p ∣ j), j)
      = p ^ L * L.factorial := by
    have hbij : (∏ j ∈ (Finset.Icc 1 (p * L)).filter (fun j => p ∣ j), j)
        = ∏ k ∈ Finset.Icc 1 L, (p * k) := by
      refine Finset.prod_nbij' (fun j => j / p) (fun k => p * k) ?_ ?_ ?_ ?_ ?_
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨⟨hj1, hj2⟩, hd⟩ := hj
        obtain ⟨k, rfl⟩ := hd
        show (p * k) / p ∈ Finset.Icc 1 L
        rw [Nat.mul_div_cancel_left k hp0, Finset.mem_Icc]
        constructor
        · rcases Nat.eq_zero_or_pos k with hk | hk
          · simp [hk] at hj1
          · exact hk
        · exact le_of_mul_le_mul_left hj2 hp0
      · rintro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, Dvd.intro k rfl⟩
        · have : 1 ≤ k := hk.1
          nlinarith [hp0]
        · exact Nat.mul_le_mul_left p hk.2
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨_, hd⟩ := hj
        show p * (j / p) = j
        exact Nat.mul_div_cancel' hd
      · rintro k _
        show (p * k) / p = k
        exact Nat.mul_div_cancel_left k hp0
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨_, hd⟩ := hj
        show j = p * (j / p)
        exact (Nat.mul_div_cancel' hd).symm
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    congr 1
    rw [← prod_Icc_eq_fact]
  rw [hfac, hsplit, hdvd, WfacN, ← mul_assoc]

/-- Cast of `factorial_block` into `ℤ_[p]`. -/
lemma factorial_block_cast (L : ℕ) :
    ((p * L).factorial : ℤ_[p]) = Wfac (p * L) * (p : ℤ_[p]) ^ L * (L.factorial : ℤ_[p]) := by
  have := factorial_block (p := p) L
  have h2 : ((p * L).factorial : ℤ_[p]) = ((WfacN (p := p) (p * L) * p ^ L * L.factorial : ℕ) : ℤ_[p]) := by
    rw [← this]
  rw [h2]; push_cast [WfacN_cast]; ring

/-- The even-case reduction of `a` to a factorial ratio. -/
lemma a_even (M : ℕ) :
    _root_.a (2 * M) =
      ((18 * M).factorial * (4 * M).factorial * (3 * M).factorial : ℝ) /
      ((9 * M).factorial * (8 * M).factorial * (6 * M).factorial * (2 * M).factorial : ℝ) := by
  unfold _root_.a
  simp only
  have h2M : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
  rw [h2M]
  have e1 : (9 : ℝ) * (2 * M) + 1 = ((18 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e2 : (2 : ℝ) * (2 * M) + 1 = ((4 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e3 : (3 / 2 : ℝ) * (2 * M) + 1 = ((3 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e4 : (9 / 2 : ℝ) * (2 * M) + 1 = ((9 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e5 : (4 : ℝ) * (2 * M) + 1 = ((8 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e6 : (3 : ℝ) * (2 * M) + 1 = ((6 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e7 : (2 * (M:ℝ)) + 1 = ((2 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6, e7, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]

/-- Numerator factorial product for the even case (at `2·M`). -/
def Neven (M : ℕ) : ℕ := (18 * M).factorial * (4 * M).factorial * (3 * M).factorial
/-- Denominator factorial product for the even case (at `2·M`). -/
def Deven (M : ℕ) : ℕ := (9 * M).factorial * (8 * M).factorial * (6 * M).factorial * (2 * M).factorial

lemma Deven_pos (M : ℕ) : 0 < Deven M := by
  unfold Deven
  positivity

/-- The integer identity `cA · Deven M = Neven M`, from `cA = a(2M)`. -/
lemma int_identity (M : ℕ) (cA : ℤ) (hA : (cA : ℝ) = _root_.a (2 * M)) :
    cA * (Deven M : ℤ) = (Neven M : ℤ) := by
  have hD : (Deven M : ℝ) ≠ 0 := by exact_mod_cast (Deven_pos M).ne'
  have hreal : (cA : ℝ) * (Deven M : ℝ) = (Neven M : ℝ) := by
    rw [hA, a_even]
    simp only [Neven, Deven]
    push_cast
    field_simp
  have : ((cA * (Deven M : ℤ) : ℤ) : ℝ) = ((Neven M : ℤ) : ℝ) := by push_cast; push_cast at hreal; linarith [hreal]
  exact_mod_cast this

/-- `Wfac` is a `p`-adic unit. -/
lemma isUnit_Wfac (m : ℕ) : IsUnit (Wfac (p := p) m) := by
  rw [PadicInt.isUnit_iff, Wfac, norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_Icc] at hi
  exact norm_cast_eq_one hi.2

/-- Per-factor block decomposition inside `ℤ_[p]`. -/
lemma fact_term (i M M' : ℕ) (hM : M = p * M') :
    ((i * M).factorial : ℤ_[p]) = Wfac (i * M) * (p : ℤ_[p]) ^ (i * M') * ((i * M').factorial : ℤ_[p]) := by
  have hiM : i * M = p * (i * M') := by rw [hM]; ring
  rw [hiM, factorial_block_cast]

/-- Numerator block decomposition. -/
lemma Neven_block (M M' : ℕ) (hM : M = p * M') :
    (Neven M : ℤ_[p]) =
      (Wfac (18 * M) * Wfac (4 * M) * Wfac (3 * M)) * (p : ℤ_[p]) ^ (25 * M') * (Neven M' : ℤ_[p]) := by
  simp only [Neven]
  push_cast
  rw [fact_term 18 M M' hM, fact_term 4 M M' hM, fact_term 3 M M' hM,
      show 25 * M' = 18 * M' + 4 * M' + 3 * M' from by ring, pow_add, pow_add]
  ring

/-- Denominator block decomposition. -/
lemma Deven_block (M M' : ℕ) (hM : M = p * M') :
    (Deven M : ℤ_[p]) =
      (Wfac (9 * M) * Wfac (8 * M) * Wfac (6 * M) * Wfac (2 * M)) * (p : ℤ_[p]) ^ (25 * M') * (Deven M' : ℤ_[p]) := by
  simp only [Deven]
  push_cast
  rw [fact_term 9 M M' hM, fact_term 8 M M' hM, fact_term 6 M M' hM, fact_term 2 M M' hM,
      show 25 * M' = 9 * M' + 8 * M' + 6 * M' + 2 * M' from by ring, pow_add, pow_add, pow_add]
  ring

/-- Finset expansion for the numerator coefficient set. -/
lemma prod_num (f : ℕ → ℤ_[p]) :
    (∏ i ∈ ({18, 4, 3} : Finset ℕ), f i) = f 18 * f 4 * f 3 := by
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

/-- Finset expansion for the denominator coefficient set. -/
lemma prod_den (f : ℕ → ℤ_[p]) :
    (∏ i ∈ ({9, 8, 6, 2} : Finset ℕ), f i) = f 9 * f 8 * f 6 * f 2 := by
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

/-- **The even-case bridge.** If `cA = a(2·m·pʳ)` and `cB = a(2·m·pʳ⁻¹)` are the
integer values of `a`, then `p^{3r} ∣ (cA - cB)`. -/
lemma even_bridge (hp5 : 5 ≤ p) (m r : ℕ) (hm : 0 < m) (hr : 1 ≤ r)
    (cA cB : ℤ) (hA : (cA : ℝ) = _root_.a (2 * (m * p ^ r)))
    (hB : (cB : ℝ) = _root_.a (2 * (m * p ^ (r - 1)))) :
    (p : ℤ) ^ (3 * r) ∣ (cA - cB) := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  set M := m * p ^ r with hMdef
  set M' := m * p ^ (r - 1) with hM'def
  have hMM' : M = p * M' := by
    rw [hMdef, hM'def]
    have hpr : p ^ r = p * p ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) from by omega]
      rw [pow_add, pow_one]
    rw [hpr]; ring
  -- integer identities from the real reduction
  have hidA : cA * (Deven M : ℤ) = (Neven M : ℤ) := int_identity M cA hA
  have hidB : cB * (Deven M' : ℤ) = (Neven M' : ℤ) := int_identity M' cB hB
  -- cast into `ℤ_[p]`
  have hidA' : (cA : ℤ_[p]) * (Deven M : ℤ_[p]) = (Neven M : ℤ_[p]) := by exact_mod_cast hidA
  have hidB' : (cB : ℤ_[p]) * (Deven M' : ℤ_[p]) = (Neven M' : ℤ_[p]) := by exact_mod_cast hidB
  rw [Neven_block M M' hMM', Deven_block M M' hMM', ← hidB'] at hidA'
  set An := Wfac (p:=p) (18 * M) * Wfac (p:=p) (4 * M) * Wfac (p:=p) (3 * M) with hAndef
  set Ad := Wfac (p:=p) (9 * M) * Wfac (p:=p) (8 * M) * Wfac (p:=p) (6 * M) * Wfac (p:=p) (2 * M) with hAddef
  set P := (p : ℤ_[p]) ^ (25 * M') with hPdef
  set Dd := (Deven M' : ℤ_[p]) with hDddef
  -- `hidA' : cA * (Ad * P * Dd) = An * P * (cB * Dd)`
  have hPne : P ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp0.ne')
  have hDdne : Dd ≠ 0 := by rw [hDddef]; exact_mod_cast (Deven_pos M').ne'
  have hPDd : P * Dd ≠ 0 := mul_ne_zero hPne hDdne
  have key : (cA : ℤ_[p]) * Ad = An * (cB : ℤ_[p]) := by
    have h2 : ((cA : ℤ_[p]) * Ad) * (P * Dd) = (An * (cB : ℤ_[p])) * (P * Dd) := by
      linear_combination hidA'
    exact mul_right_cancel₀ hPDd h2
  -- reduction `m = m₀ · p^e` with `¬ p ∣ m₀`
  obtain ⟨m₀, e, hnp, hmfac⟩ : ∃ m₀ e, ¬ p ∣ m₀ ∧ m = m₀ * p ^ e := by
    refine ⟨ordCompl[p] m, m.factorization p, Nat.not_dvd_ordCompl (Fact.out (p := p.Prime)) hm.ne', ?_⟩
    rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hMval : M = m₀ * p ^ (r + e) := by rw [hMdef, hmfac]; ring
  -- apply the strong supercongruence
  have hstrong := strong_supercongruence (p := p) hp5 ({18, 4, 3} : Finset ℕ)
    ({9, 8, 6, 2} : Finset ℕ) id m₀ (r + e) hnp (by omega) (by decide)
  have hAn : (∏ i ∈ ({18, 4, 3} : Finset ℕ), Wfac (id i * (m₀ * p ^ (r + e)))) = An := by
    rw [prod_num]; simp only [id_eq]; rw [← hMval, hAndef]
  have hAd : (∏ i ∈ ({9, 8, 6, 2} : Finset ℕ), Wfac (id i * (m₀ * p ^ (r + e)))) = Ad := by
    rw [prod_den]; simp only [id_eq]; rw [← hMval, hAddef]
  rw [hAn, hAd] at hstrong
  -- `p^{3r} ∣ (An - Ad)`
  have hpow_dvd : (p : ℤ_[p]) ^ (3 * r) ∣ (An - Ad) :=
    dvd_trans (pow_dvd_pow (p : ℤ_[p]) (by omega)) hstrong
  -- combine
  have hrel : ((cA : ℤ_[p]) - (cB : ℤ_[p])) * Ad = (cB : ℤ_[p]) * (An - Ad) := by
    rw [sub_mul, mul_sub]; rw [key]; ring
  have hAdunit : IsUnit Ad := by
    rw [hAddef]
    exact (((isUnit_Wfac _).mul (isUnit_Wfac _)).mul (isUnit_Wfac _)).mul (isUnit_Wfac _)
  have hp3r : (p : ℤ_[p]) ^ (3 * r) ∣ ((cA : ℤ_[p]) - (cB : ℤ_[p])) := by
    rw [← IsUnit.dvd_mul_right hAdunit, hrel]
    exact hpow_dvd.mul_left _
  -- convert back to `ℤ`
  have hcast : ((cA - cB : ℤ) : ℤ_[p]) = (cA : ℤ_[p]) - (cB : ℤ_[p]) := by push_cast; ring
  rw [← hcast] at hp3r
  have hnorm : ‖((cA - cB : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(3 * r : ℕ) : ℤ) :=
    (dvd_iff_norm_le _ (3 * r)).mp hp3r
  have hfin := (PadicInt.norm_int_le_pow_iff_dvd (k := cA - cB) (n := 3 * r)).mp hnorm
  exact_mod_cast hfin

end PBridge

end

section  -- ===== PBridgeOdd =====

open scoped Real

namespace PBridgeOdd

open PLog PKaz PSigma PStrong PBridge

variable {p : ℕ} [Fact p.Prime]

/-! ## Generalized factorial block for arbitrary `m`. -/

/-- The block decomposition of a factorial for arbitrary `m`:
`m! = WfacN(m) · p^{⌊m/p⌋} · ⌊m/p⌋!`. -/
lemma factorial_block_gen (m : ℕ) :
    m.factorial = WfacN (p := p) m * p ^ (m / p) * (m / p).factorial := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have hfac : m.factorial = ∏ j ∈ Finset.Icc 1 m, j := (prod_Icc_eq_fact m).symm
  have hsplit : (∏ j ∈ Finset.Icc 1 m, j)
      = (∏ j ∈ (Finset.Icc 1 m).filter (fun j => ¬ p ∣ j), j)
        * (∏ j ∈ (Finset.Icc 1 m).filter (fun j => p ∣ j), j) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 m) (fun j => p ∣ j)
        (fun j => j), mul_comm]
  have hdvd : (∏ j ∈ (Finset.Icc 1 m).filter (fun j => p ∣ j), j)
      = p ^ (m / p) * (m / p).factorial := by
    have hbij : (∏ j ∈ (Finset.Icc 1 m).filter (fun j => p ∣ j), j)
        = ∏ k ∈ Finset.Icc 1 (m / p), (p * k) := by
      refine Finset.prod_nbij' (fun j => j / p) (fun k => p * k) ?_ ?_ ?_ ?_ ?_
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨⟨hj1, hj2⟩, hd⟩ := hj
        obtain ⟨c, rfl⟩ := hd
        show (p * c) / p ∈ Finset.Icc 1 (m / p)
        rw [Nat.mul_div_cancel_left c hp0, Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rcases Nat.eq_zero_or_pos c with hk | hk
          · simp [hk] at hj1
          · exact hk
        · exact Nat.le_div_iff_mul_le hp0 |>.mpr (by rw [mul_comm]; exact hj2)
      · rintro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, Dvd.intro k rfl⟩
        · have : 1 ≤ k := hk.1
          nlinarith [hp0]
        · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp0).mp hk.2
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨_, hd⟩ := hj
        exact Nat.mul_div_cancel' hd
      · rintro k _
        exact Nat.mul_div_cancel_left k hp0
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨_, hd⟩ := hj
        exact (Nat.mul_div_cancel' hd).symm
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    congr 1
    rw [← prod_Icc_eq_fact]
  rw [hfac, hsplit, hdvd, WfacN, ← mul_assoc]

/-! ## Part 0: the real reduction of `a n` for odd `n`. -/

/-- Legendre duplication packaged for a natural half-integer point:
`Γ((m+1)+1/2) = (2m+1)! · 2^{-1-2m} · √π / m!`. -/
lemma Gamma_half_nat (m : ℕ) :
    Real.Gamma ((m : ℝ) + 1 + 1 / 2)
      = ((2 * m + 1).factorial : ℝ) * (2 : ℝ) ^ (-1 - 2 * (m : ℝ)) * Real.sqrt π
        / (m.factorial : ℝ) := by
  have hdup := Real.Gamma_mul_Gamma_add_half ((m : ℝ) + 1)
  have hGm1 : Real.Gamma ((m : ℝ) + 1) = (m.factorial : ℝ) := by
    rw [Real.Gamma_nat_eq_factorial]
  have h2s : Real.Gamma (2 * ((m : ℝ) + 1)) = ((2 * m + 1).factorial : ℝ) := by
    have : (2 : ℝ) * ((m : ℝ) + 1) = ((2 * m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [this, Real.Gamma_nat_eq_factorial]
  have hexp : (1 : ℝ) - 2 * ((m : ℝ) + 1) = -1 - 2 * (m : ℝ) := by ring
  rw [hGm1, h2s, hexp] at hdup
  have hfac_ne : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp at hdup ⊢
  linarith [hdup]

/-- `A = (9N-1)/2`. -/
def Aidx (N : ℕ) : ℕ := (9 * N - 1) / 2
/-- `B = (3N-1)/2`. -/
def Bidx (N : ℕ) : ℕ := (3 * N - 1) / 2

lemma two_Aidx (N : ℕ) (hodd : Odd N) : 2 * Aidx N + 1 = 9 * N := by
  obtain ⟨m, hm⟩ := hodd; subst hm; unfold Aidx; omega

lemma two_Bidx (N : ℕ) (hodd : Odd N) : 2 * Bidx N + 1 = 3 * N := by
  obtain ⟨m, hm⟩ := hodd; subst hm; unfold Bidx; omega

/-- The odd-case reduction of `a` to a factorial ratio.
For `n = 2k+1`, `A = 9k+4 = (9n-1)/2`, `B = 3k+1 = (3n-1)/2`. -/
lemma a_odd (k : ℕ) :
    _root_.a (2 * k + 1) =
      ((2 : ℝ) ^ (6 * (2 * k + 1)) * ((2 * (2 * k + 1)).factorial : ℝ) * ((9 * k + 4).factorial : ℝ)) /
      (((4 * (2 * k + 1)).factorial : ℝ) * ((2 * k + 1).factorial : ℝ) * ((3 * k + 1).factorial : ℝ)) := by
  set n := 2 * k + 1 with hn
  unfold _root_.a
  simp only
  have hπ : Real.sqrt π > 0 := Real.sqrt_pos.mpr Real.pi_pos
  have hπne : Real.sqrt π ≠ 0 := ne_of_gt hπ
  -- integer Gammas
  have e1 : (9 : ℝ) * (n : ℝ) + 1 = ((9 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have e2 : (2 : ℝ) * (n : ℝ) + 1 = ((2 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have e5 : (4 : ℝ) * (n : ℝ) + 1 = ((4 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have e6 : (3 : ℝ) * (n : ℝ) + 1 = ((3 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have e7 : (n : ℝ) + 1 = ((n : ℕ) : ℝ) + 1 := by push_cast; ring
  -- half Gammas
  have hB : (3 / 2 : ℝ) * (n : ℝ) + 1 = ((3 * k + 1 : ℕ) : ℝ) + 1 + 1 / 2 := by
    rw [hn]; push_cast; ring
  have hA : (9 / 2 : ℝ) * (n : ℝ) + 1 = ((9 * k + 4 : ℕ) : ℝ) + 1 + 1 / 2 := by
    rw [hn]; push_cast; ring
  rw [e1, e2, e5, e6, e7, hB, hA,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Gamma_half_nat (3 * k + 1), Gamma_half_nat (9 * k + 4)]
  -- reduce the factorials appearing after duplication
  have hB1 : 2 * (3 * k + 1) + 1 = 3 * n := by rw [hn]; ring
  have hA1 : 2 * (9 * k + 4) + 1 = 9 * n := by rw [hn]; ring
  rw [hB1, hA1]
  -- now combine 2-power terms and cancel √π, (9n)!, (3n)!
  have hfac9 : ((9 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (9 * n).factorial_ne_zero
  have hfac3 : ((3 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (3 * n).factorial_ne_zero
  have hfacB : (((3 * k + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (3 * k + 1).factorial_ne_zero
  have hfacA : (((9 * k + 4).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (9 * k + 4).factorial_ne_zero
  have hfac4 : ((4 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (4 * n).factorial_ne_zero
  have hfacn : ((n).factorial : ℝ) ≠ 0 := by exact_mod_cast (n).factorial_ne_zero
  -- 2-power identity: 2^(-1-2B) = 2^(6n) · 2^(-1-2A)
  have hpow : (2 : ℝ) ^ (-1 - 2 * ((3 * k + 1 : ℕ) : ℝ))
      = (2 : ℝ) ^ (6 * n) * (2 : ℝ) ^ (-1 - 2 * ((9 * k + 4 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) (6 * n), ← Real.rpow_add (by norm_num)]
    congr 1
    rw [hn]; push_cast; ring
  rw [hpow]
  have hcne : (2 : ℝ) ^ (-1 - 2 * ((9 * k + 4 : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp

/-! ## Part 1: the integer identity and its `ℤ_[p]` block decomposition. -/

/-- Numerator factorial product for the odd case. -/
def Numo (N : ℕ) : ℕ := 2 ^ (6 * N) * (2 * N).factorial * (Aidx N).factorial
/-- Denominator factorial product for the odd case. -/
def Deno (N : ℕ) : ℕ := (4 * N).factorial * N.factorial * (Bidx N).factorial

lemma Deno_pos (N : ℕ) : 0 < Deno N := by unfold Deno; positivity

/-- `cA · Deno N = Numo N`, from `cA = a N`, for odd `N`. -/
lemma int_identity_odd (N : ℕ) (hodd : Odd N) (cA : ℤ) (hA : (cA : ℝ) = _root_.a N) :
    cA * (Deno N : ℤ) = (Numo N : ℤ) := by
  obtain ⟨k, hk⟩ := hodd
  have hN : N = 2 * k + 1 := by omega
  subst hN
  have hAi : Aidx (2 * k + 1) = 9 * k + 4 := by unfold Aidx; omega
  have hBi : Bidx (2 * k + 1) = 3 * k + 1 := by unfold Bidx; omega
  have hD : (Deno (2 * k + 1) : ℝ) ≠ 0 := by exact_mod_cast (Deno_pos _).ne'
  have hreal : (cA : ℝ) * (Deno (2 * k + 1) : ℝ) = (Numo (2 * k + 1) : ℝ) := by
    rw [hA, a_odd k]
    unfold Numo Deno
    rw [hAi, hBi]
    push_cast
    field_simp
  have : ((cA * (Deno (2 * k + 1) : ℤ) : ℤ) : ℝ) = ((Numo (2 * k + 1) : ℤ) : ℝ) := by
    push_cast; push_cast at hreal; linarith [hreal]
  exact_mod_cast this

/-- Per-factor block decomposition, keyed on the floor `m / p = m'`. -/
lemma fact_term_div (m m' : ℕ) (h : m / p = m') :
    ((m.factorial : ℕ) : ℤ_[p]) = Wfac m * (p : ℤ_[p]) ^ m' * ((m'.factorial : ℕ) : ℤ_[p]) := by
  have := factorial_block_gen (p := p) m
  have h2 : ((m.factorial : ℕ) : ℤ_[p])
      = ((WfacN (p := p) m * p ^ (m / p) * (m / p).factorial : ℕ) : ℤ_[p]) := by rw [← this]
  rw [h2]; push_cast [WfacN_cast, h]; ring

/-- Division/quotient fact for the half indices. -/
lemma idx_div (a a' t : ℕ) (hp : p = 2 * t + 1) (hkey : 2 * a + 1 = p * (2 * a' + 1)) :
    a = p * a' + t ∧ a / p = a' := by
  have hp0 : 0 < p := by omega
  have heq2 : 2 * (p * a' + t) + 1 = 2 * a + 1 := by rw [hkey, hp]; ring
  have hae : p * a' + t = a := by
    have := Nat.add_right_cancel heq2
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  refine ⟨hae.symm, ?_⟩
  rw [← hae, Nat.mul_add_div hp0, Nat.div_eq_of_lt (by omega), Nat.add_zero]

/-- Numerator block decomposition into level `N'`. -/
lemma Numo_block (Nr N' t : ℕ) (hp : p = 2 * t + 1) (hodd : Odd Nr) (hNr : Nr = p * N') :
    (Numo Nr : ℤ_[p]) =
      (2 : ℤ_[p]) ^ (6 * (Nr - N'))
        * (Wfac (2 * Nr) * Wfac (Aidx Nr))
        * (p : ℤ_[p]) ^ (2 * N' + Aidx N') * (Numo N' : ℤ_[p]) := by
  have hp0 : 0 < p := by omega
  have hoddN' : Odd N' := by
    have hh : Odd (p * N') := hNr ▸ hodd
    exact (Nat.odd_mul.mp hh).2
  -- divisions
  have hd2 : (2 * Nr) / p = 2 * N' := by rw [hNr]; rw [show 2 * (p * N') = p * (2 * N') from by ring, Nat.mul_div_cancel_left _ hp0]
  have hdA := (idx_div (Aidx Nr) (Aidx N') t hp (by
    rw [two_Aidx Nr hodd, hNr, two_Aidx N' hoddN']; ring)).2
  have hNrge : N' ≤ Nr := by rw [hNr]; nlinarith [hp0]
  unfold Numo
  push_cast
  rw [fact_term_div (2 * Nr) (2 * N') hd2, fact_term_div (Aidx Nr) (Aidx N') hdA]
  rw [show 6 * Nr = 6 * (Nr - N') + 6 * N' from by omega, pow_add]
  ring

/-- Denominator block decomposition into level `N'`. -/
lemma Deno_block (Nr N' t : ℕ) (hp : p = 2 * t + 1) (hodd : Odd Nr) (hNr : Nr = p * N') :
    (Deno Nr : ℤ_[p]) =
      (Wfac (4 * Nr) * Wfac Nr * Wfac (Bidx Nr))
        * (p : ℤ_[p]) ^ (4 * N' + N' + Bidx N') * (Deno N' : ℤ_[p]) := by
  have hp0 : 0 < p := by omega
  have hoddN' : Odd N' := by
    have hh : Odd (p * N') := hNr ▸ hodd
    exact (Nat.odd_mul.mp hh).2
  have hd4 : (4 * Nr) / p = 4 * N' := by rw [hNr]; rw [show 4 * (p * N') = p * (4 * N') from by ring, Nat.mul_div_cancel_left _ hp0]
  have hd1 : Nr / p = N' := by rw [hNr, Nat.mul_div_cancel_left _ hp0]
  have hdB := (idx_div (Bidx Nr) (Bidx N') t hp (by
    rw [two_Bidx Nr hodd, hNr, two_Bidx N' hoddN']; ring)).2
  unfold Deno
  push_cast
  rw [fact_term_div (4 * Nr) (4 * N') hd4, fact_term_div Nr N' hd1, fact_term_div (Bidx Nr) (Bidx N') hdB]
  rw [pow_add, pow_add]
  ring

/-- Abbreviation: the analytic unit `U = 2^{6ΔN}·Wnum·Wden⁻¹`, which is `≡ 1 (mod p)`. -/
noncomputable def Ucore (n r : ℕ) : ℤ_[p] :=
  (2 : ℤ_[p]) ^ (6 * (n * p ^ r - n * p ^ (r - 1)))
      * (Wfac (2 * (n * p ^ r)) * Wfac (Aidx (n * p ^ r)))
      * PadicInt.inv (Wfac (4 * (n * p ^ r)) * Wfac (n * p ^ r) * Wfac (Bidx (n * p ^ r)))

/- **The analytic heart of the odd core (the p-adic Legendre duplication, to all orders).**

This states that the block-correction unit `Ucore` is `≡ 1 (mod p)` and that its `p`-adic
logarithm has norm `≤ p^{-3r}`.  Numerically (`p ∈ {5,7,11,13}`, various `n,r`) the log equals
`∑ₛ Σₛ · (n·2⁻¹·pʳ⁻¹)ˢ · ((18ˢ+4ˢ+3ˢ) − (9ˢ+8ˢ+6ˢ+2ˢ))`, i.e. exactly the even-case
`Sig`-series with the *half-integer* count base `h·pʳ⁻¹`, `h = n/2 ∈ ℤ_[p]`.  Since `Σ₀ = Σ₂ = 0`
and `18+4+3 = 9+8+6+2 = 25`, the `s = 0,1,2` terms vanish and each `s ≥ 3` term is bounded by
`‖Σₛ‖·‖h pʳ⁻¹‖ˢ ≤ p^{-3}·p^{-3(r-1)} = p^{-3r}`, exactly as in `PStrong.logdiff_le`.  Proving the
identity connecting `padicLog Ucore` to that series is the `p`-adic Legendre duplication formula
for Morita's `Γ_p`; this is the one remaining gap. -/
/-- The half-integer count base `M'' = n·2⁻¹·pʳ⁻¹ ∈ ℤ_[p]`. -/
noncomputable def Mbase (n r : ℕ) : ℤ_[p] := (n : ℤ_[p]) * iv 2 * (p : ℤ_[p]) ^ (r - 1)

/-- **The p-adic Legendre duplication series identity** (verified numerically for
`p ∈ {5,7,11,13}`).  The `p`-adic log of the odd-core unit `Ucore - 1` expands as the
even-case `Sig`-series evaluated at the *half-integer* count base `M'' = n·2⁻¹·pʳ⁻¹`, with
count differences `Δₛ = (18ˢ+4ˢ+3ˢ) − (9ˢ+8ˢ+6ˢ+2ˢ)`. -/
lemma Ucore_log_series (hp5 : 5 ≤ p) (n r : ℕ) (hodd : Odd n) (hn : 0 < n) (hr : 1 ≤ r) :
    ‖(Ucore (p := p) n r) - 1‖ < 1 ∧
    padicLog ((Ucore (p := p) n r) - 1)
      = ∑' s : ℕ, Sig (p := p) s
          * ((Mbase (p := p) n r : ℚ_[p]) ^ s
              * (((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s))) := by
  sorry

lemma Ucore_log_bound (hp5 : 5 ≤ p) (n r : ℕ) (hodd : Odd n) (hn : 0 < n) (hr : 1 ≤ r) :
    ‖(Ucore (p := p) n r) - 1‖ < 1 ∧
    ‖padicLog ((Ucore (p := p) n r) - 1)‖ ≤ (p : ℝ) ^ (-(3 * r : ℕ) : ℤ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hinv_le_one : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hp0]; exact_mod_cast (by omega : 1 ≤ p)
  obtain ⟨hlt, hser⟩ := Ucore_log_series hp5 n r hodd hn hr
  refine ⟨hlt, ?_⟩
  rw [hser]
  set MQ : ℚ_[p] := (Mbase (p := p) n r : ℚ_[p]) with hMQ
  -- `‖MQ‖ ≤ p^{-(r-1)}`.
  have h2nd : ¬ p ∣ 2 := by
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have hiv2norm : ‖(iv (p := p) 2 : ℤ_[p])‖ = 1 := by
    have h := mul_iv_cancel (p := p) (i := 2) h2nd
    have hc := congrArg norm h
    rw [norm_mul, norm_one, norm_cast_eq_one h2nd, one_mul] at hc
    exact hc
  have hMnorm : ‖MQ‖ ≤ ((p : ℝ)⁻¹) ^ (r - 1) := by
    rw [hMQ, PadicInt.padic_norm_e_of_padicInt, Mbase, norm_mul, norm_mul, norm_pow,
      PadicInt.norm_p, hiv2norm, mul_one]
    calc ‖(n : ℤ_[p])‖ * ((p : ℝ)⁻¹) ^ (r - 1)
        ≤ 1 * ((p : ℝ)⁻¹) ^ (r - 1) := by
          gcongr; exact PadicInt.norm_le_one _
      _ = ((p : ℝ)⁻¹) ^ (r - 1) := one_mul _
  -- `‖Δ s‖ ≤ 1` since the count difference is an integer.
  have hΔle : ∀ s : ℕ,
      ‖((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)‖ ≤ 1 := by
    intro s
    have hcast : ((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)
        = ((((18 ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)) : ℤ) : ℚ_[p]) := by
      push_cast; ring
    rw [hcast, ← PadicInt.coe_intCast, PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_le_one _
  -- the per-term bound
  have key : ∀ s : ℕ,
      ‖Sig (p := p) s
          * (MQ ^ s * (((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)))‖
        ≤ (p : ℝ) ^ (-((3 * r : ℕ) : ℤ)) := by
    intro s
    rcases Nat.lt_or_ge s 3 with hs | hs
    · interval_cases s
      · rw [Sig_zero]; simp only [zero_mul, norm_zero]; positivity
      · have hd1 : ((18 : ℚ_[p]) ^ 1 + 4 ^ 1 + 3 ^ 1) - (9 ^ 1 + 8 ^ 1 + 6 ^ 1 + 2 ^ 1) = 0 := by
          norm_num
        rw [hd1, mul_zero, mul_zero, norm_zero]; positivity
      · rw [Sig_two_eq_zero hp5]; simp only [zero_mul, norm_zero]; positivity
    · rw [norm_mul, norm_mul, norm_pow]
      have hSig : ‖Sig (p := p) s‖ ≤ ((p : ℝ)⁻¹) ^ 3 := by
        have hz3 : ((p : ℝ)⁻¹) ^ 3 = (p : ℝ) ^ (-3 : ℤ) := by rw [rpow_neg]; norm_num
        rw [hz3]; exact norm_Sig_le3 hp5 s (by omega)
      have hDs := hΔle s
      calc ‖Sig (p := p) s‖
              * (‖MQ‖ ^ s * ‖((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)‖)
          ≤ ((p : ℝ)⁻¹) ^ 3 * ((((p : ℝ)⁻¹) ^ (r - 1)) ^ s * 1) := by
            gcongr
        _ = ((p : ℝ)⁻¹) ^ (3 + (r - 1) * s) := by rw [mul_one, ← pow_mul, ← pow_add]
        _ ≤ ((p : ℝ)⁻¹) ^ (3 * r) := by
            apply pow_le_pow_of_le_one (by positivity) hinv_le_one
            have hle : (r - 1) * 3 ≤ (r - 1) * s := Nat.mul_le_mul (le_refl (r - 1)) (by omega)
            omega
        _ = (p : ℝ) ^ (-((3 * r : ℕ) : ℤ)) := rpow_neg (3 * r)
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) key

/-- **The hard `p`-adic core (odd case).**  Fully reduced to `Ucore_log_bound`. -/
lemma odd_core (hp5 : 5 ≤ p) (n r : ℕ) (hodd : Odd n) (hn : 0 < n) (hr : 1 ≤ r) :
    (p : ℤ_[p]) ^ (3 * r) ∣
      ((2 : ℤ_[p]) ^ (6 * (n * p ^ r - n * p ^ (r - 1)))
          * (Wfac (2 * (n * p ^ r)) * Wfac (Aidx (n * p ^ r)))
        - (Wfac (4 * (n * p ^ r)) * Wfac (n * p ^ r) * Wfac (Bidx (n * p ^ r)))) := by
  have hp3 : 3 ≤ p := by omega
  set Wnum := (2 : ℤ_[p]) ^ (6 * (n * p ^ r - n * p ^ (r - 1)))
      * (Wfac (2 * (n * p ^ r)) * Wfac (Aidx (n * p ^ r))) with hWnum
  set Wden := Wfac (p := p) (4 * (n * p ^ r)) * Wfac (p := p) (n * p ^ r)
      * Wfac (p := p) (Bidx (n * p ^ r)) with hWden
  have hWdenunit : IsUnit Wden :=
    ((isUnit_Wfac _).mul (isUnit_Wfac _)).mul (isUnit_Wfac _)
  have hWnorm : ‖Wden‖ = 1 := PadicInt.isUnit_iff.mp hWdenunit
  set vinv := PadicInt.inv Wden with hvinv
  have hvv : Wden * vinv = 1 := PadicInt.mul_inv hWnorm
  set U := Wnum * vinv with hU
  have hUcore : U = Ucore (p := p) n r := by
    rw [hU, hvinv, hWden, hWnum, Ucore]
  -- Wnum - Wden = (U - 1) * Wden
  have hfact : Wnum - Wden = (U - 1) * Wden := by
    rw [hU, sub_mul, one_mul, mul_assoc, mul_comm vinv Wden, hvv, mul_one]
  have hbnd := Ucore_log_bound hp5 n r hodd hn hr
  rw [← hUcore] at hbnd
  have hdvd : (p : ℤ_[p]) ^ (3 * r) ∣ (U - 1) :=
    sub_one_dvd_of_padicLog hp3 U hbnd.1 (3 * r) (by
      simpa using hbnd.2)
  rw [hfact]
  exact hdvd.mul_right _

/-- **The odd-case bridge.** -/
lemma odd_bridge (hp5 : 5 ≤ p) (n r : ℕ) (hodd : Odd n) (hn : 0 < n) (hr : 1 ≤ r)
    (cA cB : ℤ) (hA : (cA : ℝ) = _root_.a (n * p ^ r)) (hB : (cB : ℝ) = _root_.a (n * p ^ (r - 1))) :
    (p : ℤ) ^ (3 * r) ∣ (cA - cB) := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  obtain ⟨t, hpt⟩ : ∃ t, p = 2 * t + 1 := by
    obtain ⟨t, ht⟩ := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega); exact ⟨t, ht⟩
  set Nr := n * p ^ r with hNrdef
  set N' := n * p ^ (r - 1) with hN'def
  have hNrN' : Nr = p * N' := by
    rw [hNrdef, hN'def]
    have hpr : p ^ r = p * p ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) from by omega]; rw [pow_add, pow_one]
    rw [hpr]; ring
  have hoddNr : Odd Nr := by
    rw [hNrdef]; exact hodd.mul (by
      have : Odd p := ⟨t, by omega⟩
      exact this.pow)
  have hoddN' : Odd N' := by
    rw [hN'def]; exact hodd.mul (by
      have : Odd p := ⟨t, by omega⟩
      exact this.pow)
  -- integer identities
  have hidA : cA * (Deno Nr : ℤ) = (Numo Nr : ℤ) := int_identity_odd Nr hoddNr cA hA
  have hidB : cB * (Deno N' : ℤ) = (Numo N' : ℤ) := int_identity_odd N' hoddN' cB hB
  have hidA' : (cA : ℤ_[p]) * (Deno Nr : ℤ_[p]) = (Numo Nr : ℤ_[p]) := by exact_mod_cast hidA
  have hidB' : (cB : ℤ_[p]) * (Deno N' : ℤ_[p]) = (Numo N' : ℤ_[p]) := by exact_mod_cast hidB
  -- balance of exponents
  have hbal : 2 * N' + Aidx N' = 4 * N' + N' + Bidx N' := by
    have hA' := two_Aidx N' hoddN'
    have hB' := two_Bidx N' hoddN'
    omega
  rw [Numo_block Nr N' t hpt hoddNr hNrN', Deno_block Nr N' t hpt hoddNr hNrN', hbal, ← hidB'] at hidA'
  set Wnum := Wfac (p := p) (2 * Nr) * Wfac (p := p) (Aidx Nr) with hWnum
  set Wden := Wfac (p := p) (4 * Nr) * Wfac (p := p) Nr * Wfac (p := p) (Bidx Nr) with hWden
  set P := (p : ℤ_[p]) ^ (4 * N' + N' + Bidx N') with hPdef
  set Dd := (Deno N' : ℤ_[p]) with hDddef
  set pw := (2 : ℤ_[p]) ^ (6 * (Nr - N')) with hpwdef
  -- hidA' : cA * (Wden * P * Dd) = pw * Wnum * P * (cB * Dd)
  have hPne : P ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp0.ne')
  have hDdne : Dd ≠ 0 := by rw [hDddef]; exact_mod_cast (Deno_pos N').ne'
  have hPDd : P * Dd ≠ 0 := mul_ne_zero hPne hDdne
  have key : (cA : ℤ_[p]) * Wden = pw * Wnum * (cB : ℤ_[p]) := by
    have h2 : ((cA : ℤ_[p]) * Wden) * (P * Dd) = (pw * Wnum * (cB : ℤ_[p])) * (P * Dd) := by
      ring_nf
      ring_nf at hidA'
      linear_combination hidA'
    exact mul_right_cancel₀ hPDd h2
  -- core divisibility
  have hcore : (p : ℤ_[p]) ^ (3 * r) ∣ (pw * Wnum - Wden) := by
    have := odd_core hp5 n r hodd hn hr
    rw [← hNrdef, ← hN'def] at this
    exact this
  have hrel : ((cA : ℤ_[p]) - (cB : ℤ_[p])) * Wden = (cB : ℤ_[p]) * (pw * Wnum - Wden) := by
    rw [sub_mul, mul_sub, key]; ring
  have hWdenunit : IsUnit Wden := by
    rw [hWden]; exact ((isUnit_Wfac _).mul (isUnit_Wfac _)).mul (isUnit_Wfac _)
  have hp3r : (p : ℤ_[p]) ^ (3 * r) ∣ ((cA : ℤ_[p]) - (cB : ℤ_[p])) := by
    rw [← IsUnit.dvd_mul_right hWdenunit, hrel]
    exact hcore.mul_left _
  have hcast : ((cA - cB : ℤ) : ℤ_[p]) = (cA : ℤ_[p]) - (cB : ℤ_[p]) := by push_cast; ring
  rw [← hcast] at hp3r
  have hnorm : ‖((cA - cB : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(3 * r : ℕ) : ℤ) :=
    (dvd_iff_norm_le _ (3 * r)).mp hp3r
  have hfin := (PadicInt.norm_int_le_pow_iff_dvd (k := cA - cB) (n := 3 * r)).mp hnorm
  exact_mod_cast hfin

/-- **Assembly: the full conjecture** (test version; the final inlined `Spec.lean` uses the
verbatim statement at top level). -/
theorem final_thm
    (h_int : ∀ m : ℕ, _root_.a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h5 n r hn hr
  haveI : Fact p.Prime := ⟨hp⟩
  set cA : ℤ := Classical.choose (h_int (n * p ^ r)) with hcAdef
  set cB : ℤ := Classical.choose (h_int (n * p ^ (r - 1))) with hcBdef
  have hA : (cA : ℝ) = _root_.a (n * p ^ r) := Classical.choose_spec (h_int (n * p ^ r))
  have hB : (cB : ℝ) = _root_.a (n * p ^ (r - 1)) := Classical.choose_spec (h_int (n * p ^ (r - 1)))
  have hr1 : 1 ≤ r := hr
  have hdvd : (p : ℤ) ^ (3 * r) ∣ (cA - cB) := by
    rcases Nat.even_or_odd n with hev | hodd
    · -- even case
      obtain ⟨m, hm2⟩ := hev
      have hmpos : 0 < m := by omega
      have hne : n = 2 * m := by omega
      have hAe : (cA : ℝ) = _root_.a (2 * (m * p ^ r)) := by
        rw [hA, hne]; congr 1; ring
      have hBe : (cB : ℝ) = _root_.a (2 * (m * p ^ (r - 1))) := by
        rw [hB, hne]; congr 1; ring
      exact PBridge.even_bridge h5 m r hmpos hr1 cA cB hAe hBe
    · -- odd case
      exact odd_bridge h5 n r hodd hn hr1 cA cB hA hB
  exact (Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hdvd))

end PBridgeOdd


end

/-- **The A364173 supercongruence conjecture.** -/
theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h5 n r hn hr
  haveI : Fact p.Prime := ⟨hp⟩
  set cA : ℤ := Classical.choose (h_int (n * p ^ r)) with hcAdef
  set cB : ℤ := Classical.choose (h_int (n * p ^ (r - 1))) with hcBdef
  have hA : (cA : ℝ) = a (n * p ^ r) := Classical.choose_spec (h_int (n * p ^ r))
  have hB : (cB : ℝ) = a (n * p ^ (r - 1)) := Classical.choose_spec (h_int (n * p ^ (r - 1)))
  have hr1 : 1 ≤ r := hr
  have hdvd : (p : ℤ) ^ (3 * r) ∣ (cA - cB) := by
    rcases Nat.even_or_odd n with hev | hodd
    · -- even case
      obtain ⟨m, hm2⟩ := hev
      have hmpos : 0 < m := by omega
      have hne : n = 2 * m := by omega
      have hAe : (cA : ℝ) = a (2 * (m * p ^ r)) := by
        rw [hA, hne]; congr 1; ring
      have hBe : (cB : ℝ) = a (2 * (m * p ^ (r - 1))) := by
        rw [hB, hne]; congr 1; ring
      exact PBridge.even_bridge h5 m r hmpos hr1 cA cB hAe hBe
    · -- odd case
      exact PBridgeOdd.odd_bridge h5 n r hodd hn hr1 cA cB hA hB
  exact (Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hdvd))

