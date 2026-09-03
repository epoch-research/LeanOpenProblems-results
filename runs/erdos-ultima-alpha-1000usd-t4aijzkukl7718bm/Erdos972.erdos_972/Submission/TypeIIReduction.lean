import Submission.CenteredVaughan

/-! An unconditional pointwise reduction to a single centered Type-II term.
The lower bound on that term in the final criterion is an explicit hypothesis,
not a proved estimate for irrational slopes. -/
namespace Erdos972TypeIIReduction

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972ChebyshevPNT Erdos972ChebyshevRowMean
open Erdos972CenteredRowScales Erdos972CenteredVaughan Erdos972CorrelationVaughan Erdos972Topology

lemma centered_small_div_tendsto {α : ℝ} (hα : 1 ≤ α) (V : ℕ) :
    Tendsto (fun N : ℕ => small α (commonMean α N) V N/N) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hh : Tendsto (fun N : ℕ => Chebyshev.psi V*(endpointBudget α N/N)) atTop (𝓝 0) := by
    simpa using (endpointBudget_div_tendsto hα0).const_mul (Chebyshev.psi V)
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlog : 0 ≤ Real.log (α*N) := Real.log_nonneg (by nlinarith)
  obtain ⟨hρ0, hρ7⟩ := psi_ratio_bounds (show 0 < α*N by positivity)
  have hs := small_bound hα hρ0 hρ7 V hN
  have hbudget : Real.log (α*N)+7 ≤ endpointBudget α N := by
    unfold endpointBudget
    nlinarith [Real.log_natCast_nonneg N]
  have hs' := hs.trans (mul_le_mul_of_nonneg_left hbudget (Chebyshev.psi_nonneg _))
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hN0.le]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hs' hN0.le

lemma centered_main_div_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (fun N : ℕ => commonMean α N*Chebyshev.psi N/N) atTop (𝓝 1) := by
  have hh := (commonMean_tendsto hα).mul (psi_div_self_tendsto.comp tendsto_natCast_atTop_atTop)
  simpa only [one_mul, Function.comp_def, mul_div_assoc] using hh

/-- At arbitrarily large cutoffs, the correlation is approximated to sublinear
accuracy by its centered main term plus the genuine Type-II sum. Both Type-I
terms have been estimated unconditionally. -/
theorem exists_correlation_bilinear_approx {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (U V : ℕ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B < N ∧
      |mangoldtCorrelation α N-commonMean α N*Chebyshev.psi N-bilinear α (commonMean α N) U V N| ≤ ε*N := by
  have hsmall : ∀ᶠ N : ℕ in atTop, |small α (commonMean α N) V N| ≤ (ε/2)*N := by
    have hh : Tendsto (fun N : ℕ => |small α (commonMean α N) V N/N|) atTop (𝓝 0) := by
      simpa using (centered_small_div_tendsto hα.le V).abs
    filter_upwards [(tendsto_order.mp hh).2 (ε/2) (by positivity), eventually_ge_atTop (1 : ℕ)] with N hN hN1
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN1
    rw [abs_div, abs_of_nonneg hN0.le] at hN
    exact ((div_lt_iff₀ hN0).mp hN).le
  obtain ⟨T, hT⟩ := eventually_atTop.mp hsmall
  obtain ⟨N, hN, htypeI⟩ := exists_small_typeI hα hI U V (show 0 < ε/2 by positivity) (max B T)
  have hNT : T ≤ N := (le_max_right _ _).trans hN.le
  refine ⟨N, (le_max_left _ _).trans_lt hN, ?_⟩
  rw [centered_vaughan_identity]
  have he (a b c d : ℝ) : a-b+c+d-d = a-b+c := by ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans (by linarith [hT N hNT])

/-- A counterexample would force the centered Type-II term arbitrarily close
to `-N` along the common good scales, for every fixed choice of cutoffs. -/
theorem finite_primeSet_forces_negative_typeII {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hfin : (primeSet α).Finite) (U V : ℕ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ |bilinear α (commonMean α N) U V N/N+1| ≤ ε := by
  have hc := finite_primeSet_correlation_tendsto_zero hα.le hfin
  have hm := centered_main_div_tendsto (show 0 < α by linarith)
  have hlim : Tendsto (fun N : ℕ => mangoldtCorrelation α N/N-commonMean α N*Chebyshev.psi N/N+1)
      atTop (𝓝 0) := by simpa using (hc.sub hm).add_const 1
  have hgood : ∀ᶠ N : ℕ in atTop,
      |mangoldtCorrelation α N/N-commonMean α N*Chebyshev.psi N/N+1| ≤ ε/2 := by
    have hh : Tendsto (fun N : ℕ => |mangoldtCorrelation α N/N-commonMean α N*Chebyshev.psi N/N+1|)
        atTop (𝓝 0) := by simpa using hlim.abs
    filter_upwards [(tendsto_order.mp hh).2 (ε/2) (by positivity)] with N hN
    exact hN.le
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgood
  obtain ⟨N, hN, herr⟩ := exists_correlation_bilinear_approx hα hI U V (show 0 < ε/2 by positivity) (max B (max T 0))
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr ((le_max_right T 0).trans_lt ((le_max_right B _).trans_lt hN))
  have hTN : T ≤ N := (le_max_left T 0).trans ((le_max_right B _).trans hN.le)
  have he : |(mangoldtCorrelation α N-commonMean α N*Chebyshev.psi N-bilinear α (commonMean α N) U V N)/N| ≤ ε/2 := by
    rw [abs_div, abs_of_nonneg hN0.le]
    exact (div_le_iff₀ hN0).mpr herr
  have hdecomp : bilinear α (commonMean α N) U V N/N+1 =
      (mangoldtCorrelation α N/N-commonMean α N*Chebyshev.psi N/N+1)-
        (mangoldtCorrelation α N-commonMean α N*Chebyshev.psi N-bilinear α (commonMean α N) U V N)/N := by ring
  refine ⟨N, (le_max_left _ _).trans_lt hN, ?_⟩
  rw [hdecomp]
  exact (abs_sub _ _).trans (by linarith [hT N hTN])

/-- A uniform lower bound separated from `-N` for just one fixed centered
Type-II sum would settle the conjecture at the given irrational slope. -/
theorem infinite_primeSet_of_typeII_gap {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (U V : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᶠ N : ℕ in atTop, -(1-δ)*N ≤ bilinear α (commonMean α N) U V N) :
    (primeSet α).Infinite := by
  intro hfin
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgap
  obtain ⟨N, hN, herr⟩ := finite_primeSet_forces_negative_typeII hα hI hfin U V
    (show 0 < δ/2 by positivity) (max T 0)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr ((le_max_right _ _).trans_lt hN)
  have hg := hT N ((le_max_left _ _).trans hN.le)
  have hh : δ ≤ bilinear α (commonMean α N) U V N/N+1 := by
    have hdiv := (le_div_iff₀ hN0).mpr hg
    linarith
  linarith [(abs_le.mp herr).2]

#print axioms exists_correlation_bilinear_approx
#print axioms finite_primeSet_forces_negative_typeII
#print axioms infinite_primeSet_of_typeII_gap

end Erdos972TypeIIReduction
