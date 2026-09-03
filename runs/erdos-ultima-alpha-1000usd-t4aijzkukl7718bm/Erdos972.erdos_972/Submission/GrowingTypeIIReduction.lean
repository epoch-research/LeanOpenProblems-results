import Submission.GrowingTypeI
import Submission.TypeIIReduction

/-! The remaining Type-II obstruction with both Vaughan cutoffs growing.
No lower bound on that obstruction is asserted without a hypothesis. -/
namespace Erdos972GrowingTypeIIReduction

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972ChebyshevRowMean Erdos972CenteredRowScales
open Erdos972CenteredVaughan Erdos972GrowingTypeI Erdos972PolynomialRowScales
open Erdos972TypeIIReduction Erdos972CorrelationVaughan Erdos972Topology

/-- Uniform approximation by the genuine Type-II term at a power-growing
family of Vaughan cutoffs. -/
theorem exists_growing_bilinear_approx {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ root64 u ≤ N ∧
      ∀ U V : ℕ, U ≤ root64 u → V ≤ root64 u → U*V ≤ root64 u →
        |mangoldtCorrelation α N-commonMean α N*Chebyshev.psi N-
          bilinear α (commonMean α N) U V N| ≤ ε*N := by
  obtain ⟨u, N, hu, hN, hvN, htypeI⟩ := exists_growing_typeI_scale hα hI hε B
  refine ⟨u, N, hu, hN, hvN, ?_⟩
  intro U V hU hV hUV
  have hh := htypeI U V hU hV hUV
  rw [centered_vaughan_identity]
  have he (a b c d : ℝ) : a-b+c+d-d = a-b+c := by ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans hh

/-- The square-root choice gives two simultaneous growing cutoffs. -/
def growingCutoff (u : ℕ) : ℕ := Nat.sqrt (root64 u)

lemma growingCutoff_eligible (u : ℕ) :
    growingCutoff u ≤ root64 u ∧ growingCutoff u*growingCutoff u ≤ root64 u := by
  exact ⟨Nat.sqrt_le_self _, by simpa only [growingCutoff, pow_two] using Nat.sqrt_le' (root64 u)⟩

lemma growingCutoff_tendsto : Tendsto growingCutoff atTop atTop := by
  refine tendsto_atTop.2 (fun B => ?_)
  filter_upwards [root64_tendsto.eventually_ge_atTop (B^2)] with u hu
  exact Nat.le_sqrt'.mpr hu

/-- Any counterexample forces the Type-II term close to `-N`, even when
both cutoffs tend to infinity at a fixed power-root rate. -/
theorem finite_primeSet_forces_growing_negative_typeII {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hfin : (primeSet α).Finite) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < growingCutoff u ∧
      |bilinear α (commonMean α N) (growingCutoff u) (growingCutoff u) N/N+1| ≤ ε := by
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
  obtain ⟨W, hW⟩ := eventually_atTop.mp (growingCutoff_tendsto.eventually_gt_atTop B)
  let C := max B (max T (max W (⌈α⌉₊+1)))
  obtain ⟨u, N, hu, rfl, hvN, herr⟩ := exists_growing_bilinear_approx hα hI (show 0 < ε/2 by positivity) C
  have hu0 : 0 < u := lt_of_le_of_lt (Nat.zero_le C) hu
  have hαu : α ≤ u := by
    apply (Nat.le_ceil α).trans
    have hh : ⌈α⌉₊+1 ≤ C := (le_max_right W _).trans ((le_max_right T _).trans (le_max_right B _))
    exact_mod_cast (Nat.le_succ ⌈α⌉₊).trans (hh.trans hu.le)
  have huN := (scaleCutoff_bounds hα.le hu0 hαu).1
  have hTN : T ≤ scaleCutoff α u := (le_max_left T _).trans ((le_max_right B _).trans (hu.le.trans huN))
  have hN0 : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr (hu0.trans_le huN)
  have helig := growingCutoff_eligible u
  have hb := herr (growingCutoff u) (growingCutoff u) helig.1 helig.1 helig.2
  have hdiv : |(mangoldtCorrelation α (scaleCutoff α u)-commonMean α (scaleCutoff α u)*Chebyshev.psi (scaleCutoff α u)-
      bilinear α (commonMean α (scaleCutoff α u)) (growingCutoff u) (growingCutoff u) (scaleCutoff α u))/(scaleCutoff α u)| ≤ ε/2 := by
    rw [abs_div, abs_of_nonneg hN0.le]
    exact (div_le_iff₀ hN0).mpr hb
  refine ⟨u, scaleCutoff α u, (le_max_left B _).trans_lt hu, rfl,
    hW u ((le_max_left W _).trans ((le_max_right T _).trans ((le_max_right B _).trans hu.le))), ?_⟩
  have he (a b c d : ℝ) : c/d+1 = (a/d-b/d+1)-(a-b-c)/d := by ring
  rw [he (mangoldtCorrelation α (scaleCutoff α u))
    (commonMean α (scaleCutoff α u)*Chebyshev.psi (scaleCutoff α u))]
  exact (abs_sub _ _).trans (by linarith only [hT _ hTN, hdiv])

/-- A lower bound separated from the parity boundary for the moving Type-II
term would suffice. The required gap remains an explicit hypothesis. -/
theorem infinite_primeSet_of_growing_typeII_gap {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᶠ u : ℕ in atTop, -(1-δ)*(scaleCutoff α u : ℝ) ≤
      bilinear α (commonMean α (scaleCutoff α u)) (growingCutoff u) (growingCutoff u) (scaleCutoff α u)) :
    (primeSet α).Infinite := by
  intro hfin
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgap
  obtain ⟨u, N, hu, rfl, hcut, herr⟩ := finite_primeSet_forces_growing_negative_typeII hα hI hfin
    (show 0 < δ/2 by positivity) (max T (⌈α⌉₊+1))
  have hu0 : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hu
  have hαu : α ≤ u := by
    apply (Nat.le_ceil α).trans
    exact_mod_cast (Nat.le_succ ⌈α⌉₊).trans ((le_max_right T _).trans hu.le)
  have hN0 : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr
    (hu0.trans_le (scaleCutoff_bounds hα.le hu0 hαu).1)
  have hg := hT u ((le_max_left T _).trans hu.le)
  have hh := (le_div_iff₀ hN0).mpr hg
  have ha := (abs_le.mp herr).2
  linarith only [hh, ha, hδ]

#print axioms infinite_primeSet_of_growing_typeII_gap

#print axioms exists_growing_bilinear_approx
#print axioms finite_primeSet_forces_growing_negative_typeII

end Erdos972GrowingTypeIIReduction
