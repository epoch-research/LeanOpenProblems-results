import Submission.HarmonicComparisonApproximation

/-! Bounded natural-mean cancellation implies harmonic-mean cancellation.
No reverse Tauberian implication is asserted. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma harmonicMean_zero_of_prefixMean_zero (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1)
    (hzero : Tendsto (fun N => prefixMean N F) atTop (𝓝 0)) :
    Tendsto (fun N => harmonicMean (N+1) F) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((hzero.abs).eventually_lt_const
    (show |(0 : ℝ)| < ε/4 by simpa using (show (0 : ℝ)<ε/4 by positivity)))
  have ht : Tendsto (fun N : ℕ => ((harmonic T : ℝ)+2)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  filter_upwards [eventually_ge_atTop T,ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with N hNT ht
  have he (i : Fin (N+1)) : |prefixMean (harmonicPrefixLength N i) F| ≤
      ε/4+(if harmonicPrefixLength N i < T then (1 : ℝ) else 0) := by
    by_cases hi : harmonicPrefixLength N i < T
    · rw [if_pos hi]
      exact (abs_prefixMean_le _ (harmonicPrefixLength_pos N i) F 1 (fun n _ => hF n)).trans (by linarith)
    · rw [if_neg hi,add_zero]
      exact (hT _ (not_lt.mp hi)).le
  have hm := (abs_mean_le_mean_abs (harmonicPrefixLaw N)
    (fun i => prefixMean (harmonicPrefixLength N i) F)).trans (mean_mono _ _ _ he)
  rw [harmonicPrefixLaw_representation,mean_add,mean_const] at hm
  have hmass := harmonicPrefixLaw_short_length_mass N T (by omega)
  have hrange : |harmonicRangeMean (N+1) F| ≤ ε/4+(harmonic T : ℝ)/(harmonic (N+1) : ℝ) := by
    exact hm.trans (by linarith)
  have herr := harmonicMean_range_error N F hF
  have htri := abs_sub_le (harmonicMean (N+1) F) (harmonicRangeMean (N+1) F) 0
  simp only [sub_zero] at htri
  rw [abs_sub_comm] at herr
  rw [Real.dist_eq,sub_zero]
  rw [add_div] at ht
  linarith

#print axioms harmonicMean_zero_of_prefixMean_zero
end Erdos371.FiniteInformation
