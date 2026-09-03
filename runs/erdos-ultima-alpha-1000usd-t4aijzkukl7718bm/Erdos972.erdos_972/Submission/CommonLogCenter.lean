import Submission.CorrelationVaughan
import Submission.ChebyshevRowMean

/-! A common logarithmic center and a bounded reciprocal Möbius sum. Keeping
these main terms signed avoids multiplying a qualitative PNT error by the
number of Type-I rows. -/
namespace Erdos972CommonLogCenter

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta Topology
open Erdos972CorrelationVaughan Erdos972ChebyshevPNT Erdos972ChebyshevRowMean Erdos972SelfCenteredLog

lemma moebius_floor_sum {N : ℕ} (hN : 0 < N) :
    (∑ m ∈ Ioc 0 N, (μ m : ℝ)*(N/m : ℕ)) = 1 := by
  have hh := weightedSum_convolution (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ) (fun _ => 1) N
  rw [coe_moebius_mul_coe_zeta] at hh
  have hleft : weightedSum (1 : ArithmeticFunction ℝ) (fun _ => 1) N = 1 := by
    simp only [weightedSum, one_apply, mul_one, sum_ite_eq', mem_Ioc]
    simp [Nat.ne_of_gt hN]
  have hinner (m : ℕ) : (∑ n ∈ Ioc 0 (N/m), (ζ : ArithmeticFunction ℝ) n*1) = (N/m : ℕ) := by
    have hz (n : ℕ) (hn : n ∈ Ioc 0 (N/m)) : (ζ : ArithmeticFunction ℝ) n = 1 := by
      simp only [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1), Nat.cast_one]
    calc
      _ = ∑ n ∈ Ioc 0 (N/m), (1 : ℝ) := sum_congr rfl (fun n hn => by rw [hz n hn, one_mul])
      _ = _ := by simp
  simp only [hleft, hinner, intCoe_apply] at hh
  exact hh.symm

/-- A simple uniform bound, retaining the sign of the Möbius coefficients. -/
lemma reciprocal_moebius_sum_bound (N : ℕ) : |∑ m ∈ Ioc 0 N, (μ m : ℝ)/m| ≤ 2 := by
  by_cases hN : N = 0
  · simp [hN]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hfrac (m : ℕ) : 0 ≤ (N : ℝ)/m-(N/m : ℕ) ∧ (N : ℝ)/m-(N/m : ℕ) ≤ 1 := by
    refine ⟨sub_nonneg.mpr Nat.cast_div_le, ?_⟩
    have hh := Nat.lt_floor_add_one ((N : ℝ)/m)
    rw [Nat.floor_div_natCast, Nat.floor_natCast] at hh
    linarith
  have he : (N : ℝ)*(∑ m ∈ Ioc 0 N, (μ m : ℝ)/m)-1 =
      ∑ m ∈ Ioc 0 N, (μ m : ℝ)*((N : ℝ)/m-(N/m : ℕ)) := by
    rw [← moebius_floor_sum hNpos, mul_sum]
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro m hm
    ring
  have hb : |(N : ℝ)*(∑ m ∈ Ioc 0 N, (μ m : ℝ)/m)-1| ≤ N := by
    rw [he]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ m ∈ Ioc 0 N, (1 : ℝ) := by
        apply sum_le_sum
        intro m hm
        rw [abs_mul, abs_of_nonneg (hfrac m).1]
        have hμ : |(μ m : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := m)
        exact (mul_le_mul hμ (hfrac m).2 (hfrac m).1 (by norm_num)).trans_eq (by norm_num)
      _ = _ := by simp
  have ht := abs_add_le ((N : ℝ)*(∑ m ∈ Ioc 0 N, (μ m : ℝ)/m)-1) 1
  rw [sub_add_cancel, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N), abs_one] at ht
  nlinarith

noncomputable def logMass (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, Real.log n

/-- Elementary logarithmic factorial bounds, from monotone sum-integral
comparison. They are uniform, not just asymptotic. -/
lemma logMass_error_bounds {N : ℕ} (hN : 0 < N) :
    0 ≤ logMass N-((N : ℝ)*Real.log N-N) ∧
      logMass N-((N : ℝ)*Real.log N-N) ≤ 1+Real.log N := by
  have hm : MonotoneOn Real.log (Set.Icc (1 : ℝ) N) := by
    intro x hx y hy hxy
    exact Real.log_le_log (by linarith [hx.1]) hxy
  have hl := MonotoneOn.sum_le_integral_Ico (a := 1) (b := N) (f := Real.log) hN (by simpa using hm)
  have hu := MonotoneOn.integral_le_sum_Ico (a := 1) (b := N) (f := Real.log) hN (by simpa using hm)
  have he : logMass N = ∑ n ∈ Ico 1 (N+1), Real.log n := by
    unfold logMass
    rw [← Ico_add_one_add_one_eq_Ioc]
    rfl
  have hshift : (∑ n ∈ Ico 1 N, Real.log (n+1 : ℕ)) = logMass N := by
    rw [sum_Ico_add' (fun n : ℕ => Real.log n) 1 N 1]
    rw [he, sum_eq_sum_Ico_succ_bot (show 1 < N+1 by omega)]
    simp
  have hsum : (∑ n ∈ Ico 1 N, Real.log n) = logMass N-Real.log N := by
    rw [he, sum_Ico_succ_top hN, add_sub_cancel_right]
  rw [hshift, integral_log] at hu
  rw [hsum, integral_log] at hl
  norm_num only [Nat.cast_one, Real.log_one, mul_zero, sub_zero] at hu hl
  constructor <;> linarith

noncomputable def commonLogCenterNat (N : ℕ) : ℝ :=
  logRow (fun n => vonMangoldt n) N-(Real.log N-1)*Chebyshev.psi N

lemma logIncrement_psi (N : ℕ) :
    logIncrement (fun n : ℕ => Chebyshev.psi n) N = logRow (fun n => vonMangoldt n) N := by
  have hzero : Chebyshev.psi (0 : ℕ) = 0 := by simp [Chebyshev.psi]
  have hh := logRow_prefix_approx (fun n => vonMangoldt n) (fun n : ℕ => Chebyshev.psi n) hzero N 0 (by
    intro j hj
    simp only [Chebyshev.psi, Nat.floor_natCast, sub_self, abs_zero, le_refl])
  simp only [mul_zero, abs_nonpos_iff] at hh
  exact (sub_eq_zero.mp hh).symm

lemma commonLogCenterNat_bound {N : ℕ} (hN : 0 < N) :
    |commonLogCenterNat N| ≤ |selfCenteredLog (fun n : ℕ => Chebyshev.psi n) N|+7*(1+Real.log N) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hρ := psi_ratio_bounds hN0
  have hmass := logMass_error_bounds hN
  have he : commonLogCenterNat N = selfCenteredLog (fun n : ℕ => Chebyshev.psi n) N+
      (Chebyshev.psi N/N)*(logMass N-((N : ℝ)*Real.log N-N)) := by
    have hh : selfCenteredLog (fun n : ℕ => Chebyshev.psi n) N =
        logIncrement (fun n : ℕ => Chebyshev.psi n) N-(Chebyshev.psi N/N)*logMass N := by
      simp only [selfCenteredLog, logIncrement, logMass,
        Erdos972ExponentialSum.sum_Ioc_zero_eq_sum_range_succ, mul_sub, sum_sub_distrib, ← sum_mul]
      ring
    rw [hh, logIncrement_psi]
    unfold commonLogCenterNat
    field_simp
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  rw [abs_mul, abs_of_nonneg hρ.1, abs_of_nonneg hmass.1]
  exact mul_le_mul hρ.2 hmass.2 hmass.1 (by norm_num)

/-- The common scalar left after the logarithmic row centers are aligned is
sublinear, using only qualitative PNT. -/
theorem commonLogCenterNat_div_tendsto :
    Tendsto (fun N : ℕ => commonLogCenterNat N/N) atTop (𝓝 0) := by
  have hs := selfCenteredLog_div_tendsto (fun n : ℕ => Chebyshev.psi n)
    (by simp [Chebyshev.psi]) (psi_div_self_tendsto.comp tendsto_natCast_atTop_atTop)
  have hs' : Tendsto (fun N : ℕ => |selfCenteredLog (fun n : ℕ => Chebyshev.psi n) N|/N) atTop (𝓝 0) := by
    simpa only [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), abs_zero] using hs.abs
  have hl : Tendsto (fun N : ℕ => Real.log N/N) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  have hh : Tendsto (fun N : ℕ => |selfCenteredLog (fun n : ℕ => Chebyshev.psi n) N|/N+7*((1+Real.log N)/N))
      atTop (𝓝 0) := by
    have hc := (tendsto_const_div_atTop_nhds_zero_nat 1).add hl
    simpa only [← add_div, mul_zero, add_zero] using hs'.add (hc.const_mul 7)
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  have hb := div_le_div_of_nonneg_right (commonLogCenterNat_bound hN) (Nat.cast_nonneg (α := ℝ) N)
  simpa only [add_div, mul_div_assoc] using hb

#print axioms reciprocal_moebius_sum_bound
#print axioms logMass_error_bounds
#print axioms commonLogCenterNat_div_tendsto

end Erdos972CommonLogCenter
