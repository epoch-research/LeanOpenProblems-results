import Submission.LocalDivisorScaleFamily

/-! Divisor-scale exact-count peaks for every critical power sum. They remain
strictly weaker than the positive-power peaks in the original conjecture. -/
namespace Erdos322Research.LocalDivisorScalePeaks
noncomputable section
open Finset Filter LocalDivisorScaleFamily
open scoped Classical Topology
set_option maxHeartbeats 0
set_option Elab.async false

/-- The height relation n <= r^(A*r) controls log(n)/log(log(n)) linearly
in r once log(log(n)) >= 1. A two-case comparison avoids any calculus. -/
lemma logarithmic_height_bound (A r n : ℕ) (hA : 1 ≤ A) (hr : 0 < r)
    (hn : 0 < n) (hlog : 1 ≤ Real.log (Real.log (n : ℝ)))
    (hheight : n ≤ r^(A*r)) :
    Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤ (A : ℝ)*r := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hLpos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  apply (div_le_iff₀ hLpos).mpr
  by_cases hsmall : Real.log (n : ℝ) ≤ r
  · have hscale : (r : ℝ) ≤ (A : ℝ)*r := by nlinarith
    have hprod : (A : ℝ)*r ≤ ((A : ℝ)*r)*Real.log (Real.log (n : ℝ)) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A) hrp.le]
    exact hsmall.trans (hscale.trans hprod)
  · have hrl : Real.log (r : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log hrp (le_of_not_ge hsmall)
    have hh : Real.log (n : ℝ) ≤ ((A : ℝ)*r)*Real.log (r : ℝ) := by
      have hcast : (n : ℝ) ≤ (r : ℝ)^(A*r) := by exact_mod_cast hheight
      have hh := Real.log_le_log hnp hcast
      simpa only [Real.log_pow, Nat.cast_mul] using hh
    exact hh.trans (mul_le_mul_of_nonneg_left hrl (by positivity))

/-- Auxiliary form indexed by k+2. -/
theorem exp_log_div_loglog_peaks_aux (k : ℕ) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
        Erdos322.representationCount (k+2) n}.Infinite := by
  let A := heightExponent k
  have hA : 1 ≤ A := by dsimp [A,heightExponent]; omega
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  let c : ℝ := Real.log 2 / A
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num)) hApos
  refine ⟨c,hc,Set.infinite_of_forall_exists_gt ?_⟩
  have ht : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  intro b
  let T := max N (b+1)
  let D := (range T).sup (Erdos322.representationCount (k+2))
  obtain ⟨r,n,hR,hkr,hn,hcount,hheight⟩ := divisor_scale_family k (D+1)
  have hr : 0 < r := by omega
  have hnT : T ≤ n := by
    by_contra hh
    have hnmem : n ∈ range T := mem_range.mpr (by omega)
    have hbd : Erdos322.representationCount (k+2) n ≤ D := le_sup hnmem
    have htwr : r < 2^r := Nat.lt_two_pow_self
    omega
  have hlog : 1 ≤ Real.log (Real.log (n : ℝ)) := hN n ((le_max_left _ _).trans hnT)
  have hbound := logarithmic_height_bound A r n hA hr hn hlog hheight
  have hexp : Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) ≤ (2 : ℝ)^r := by
    calc
      _ ≤ Real.exp (c*((A : ℝ)*r)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbound hc.le)
      _ = Real.exp ((r : ℝ)*Real.log 2) := by
        congr 1
        dsimp only [c]
        field_simp
      _ = (2 : ℝ)^r := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  refine ⟨n,hexp.trans_lt (by exact_mod_cast hcount),?_⟩
  have hbT : b+1 ≤ T := le_max_right _ _
  omega

/-- Every critical power-sum count with k >= 2 has infinitely many peaks
of size exp(c log(n)/log(log(n))). This does not give any fixed n^epsilon. -/
theorem exp_log_div_loglog_peaks (k : ℕ) (hk : 2 ≤ k) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
        Erdos322.representationCount k n}.Infinite := by
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hk
  have h : k=j+2 := by omega
  rw [h]
  exact exp_log_div_loglog_peaks_aux j

end
end Erdos322Research.LocalDivisorScalePeaks
