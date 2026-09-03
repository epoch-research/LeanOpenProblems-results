import Submission.AsymmetricDiagonalBudget

/-! Small equal-factor diagonal and both one-prime row families on a common
irrational scale. This does not settle the remaining off-diagonal sum. -/
namespace Erdos972CommonAsymmetricDiagonal

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972AsymmetricDiagonalBudget Erdos972VaughanDiagonalBound
open Erdos972PolynomialRowScales Erdos972CenteredRowScales
open Erdos972ReciprocalDivisorCounts Erdos972RationalRotationCount
open Erdos972DualPrimeRows Erdos972InverseGoodApproximation
open Erdos972ScaledPrimeRows Erdos972DirectRowApproximation
open Erdos972CommonCovarianceScales Erdos972DivisorPairCount
open Erdos972WeightedPrimeRotation Erdos972BeattyRows

set_option maxHeartbeats 1500000
attribute [local irreducible] root64

lemma inverse_diagonal_data {α : ℝ} (hα : 1 ≤ α) (r : ℚ)
    (hr : |1/α-r| ≤ 1/(r.den : ℝ)^2) {u : ℕ}
    (hu : 0 < u) (hαu : 4*α ≤ u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4) :
    ∃ a q : ℕ, 0 < q ∧ a.Coprime q ∧
      (u : ℝ)^4 ≤ 2*α*q ∧ (q : ℝ) ≤ 32*(u : ℝ)^4 ∧
      |α-(a : ℝ)/q| * (scaleCutoff α u : ℝ) ≤ 1 ∧
      scaleCutoff α u ≤ q^2 := by
  have hα0 : 0 < α := by linarith
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hαu' : α ≤ u := by linarith
  have hloR : (u : ℝ)^4 ≤ r.den := by exact_mod_cast hlo
  have hhiR : (r.den : ℝ) ≤ 16*(u : ℝ)^4 := by exact_mod_cast hhi
  have hu4 : (u : ℝ) ≤ (u : ℝ)^4 := by
    exact_mod_cast Nat.le_self_pow (by norm_num : 4 ≠ 0) u
  have hrd : 2*α ≤ r.den := by linarith only [hαu, hu4, hloR, hα0]
  obtain ⟨hspos, hslo, hshi, herr⟩ := inverse_approximant_bounds hα r hr hrd
  let s := r⁻¹
  have heq : (s : ℝ) = (s.num.natAbs : ℝ)/s.den :=
    nonneg_rat_cast_eq_natAbs_div s hspos.le
  have hsqlow : (u : ℝ)^4 ≤ 2*α*s.den := by
    have hh := (div_le_iff₀ (show 0 < 2*α by positivity)).mp hslo
    linarith only [hh, hloR]
  have hsqhigh : (s.den : ℝ) ≤ 32*(u : ℝ)^4 := by
    linarith only [hshi, hhiR]
  have hNr : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6 := by
    exact_mod_cast (scaleCutoff_bounds hα hu hαu').2.1
  have hu2 : 4*α^2 ≤ (u : ℝ)^2 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ 2*α by positivity)
      (show 2*α ≤ (u : ℝ) by linarith) 2
    nlinarith only [hh]
  have hu8 : (u : ℝ)^8 ≤ (r.den : ℝ)^2 := by
    have hh := pow_le_pow_left₀ (pow_nonneg huR.le 4) hloR 2
    nlinarith only [hh]
  have hNsmall : 2*α^2*(scaleCutoff α u : ℝ) ≤ (r.den : ℝ)^2 := by
    calc
      _ ≤ 2*α^2*(u : ℝ)^6 := mul_le_mul_of_nonneg_left hNr (by positivity)
      _ ≤ (u : ℝ)^2*(u : ℝ)^6 := by gcongr; nlinarith only [hu2, sq_nonneg α]
      _ = (u : ℝ)^8 := by ring
      _ ≤ _ := hu8
  have hrdR : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hsmall : |α-(s : ℝ)| * (scaleCutoff α u : ℝ) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg (α := ℝ) (scaleCutoff α u))
    apply hh.trans
    calc
      _ = (2*α^2*(scaleCutoff α u : ℝ))/(r.den : ℝ)^2 := by ring
      _ ≤ 1 := (div_le_one (sq_pos_of_pos hrdR)).mpr hNsmall
  have hNsq : scaleCutoff α u ≤ s.den^2 := by
    have hsq : (u : ℝ)^8 ≤ 4*α^2*(s.den : ℝ)^2 := by
      have hh := pow_le_pow_left₀ (pow_nonneg huR.le 4) hsqlow 2
      nlinarith only [hh]
    have hNN : 4*α^2*(scaleCutoff α u : ℝ) ≤ 4*α^2*(s.den : ℝ)^2 := by
      calc
        _ ≤ 4*α^2*(u : ℝ)^6 := mul_le_mul_of_nonneg_left hNr (by positivity)
        _ ≤ (u : ℝ)^2*(u : ℝ)^6 := mul_le_mul_of_nonneg_right hu2 (by positivity)
        _ = (u : ℝ)^8 := by ring
        _ ≤ _ := hsq
    have hh := (mul_le_mul_iff_right₀ (show 0 < 4*α^2 by positivity)).mp hNN
    exact_mod_cast hh
  refine ⟨s.num.natAbs, s.den, s.pos, s.reduced, hsqlow, hsqhigh, ?_, hNsq⟩
  rw [← heq]
  exact hsmall

/-- The diagonal estimate is selected together with both prime-row families
and the joint small-divisor estimates, not on an unrelated sequence. -/
theorem exists_two_sided_scale_small_diagonal {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < mobiusCutoff u ∧ 4*α ≤ u ∧
      2048*dualScaleLoss α ≤ root64 u ∧ OutputPrimeScale α u ∧
      (∀ e : ℕ, 0 < e → e ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
        |inputDivisorRow α e X-Chebyshev.psi X/e| ≤ scaledRowError (dualScaleLoss α) u (root64 u)) ∧
      (∀ d e : ℕ, 0 < d → 0 < e → e ≤ root64 u → ∀ X ≤ scaleCutoff α u,
        |((divisorPairs α X d e).card : ℝ)-(X : ℝ)/(d*e)| ≤ 118*(root64 u : ℝ)*(u : ℝ)^4) ∧
      |vaughanDiagonal α (scaleCutoff α u) (mobiusCutoff u) (mangoldtCutoff u)| ≤
        ε*(scaleCutoff α u : ℝ) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_small_diagonal hα.le hε).and (mobiusCutoff_tendsto.eventually_gt_atTop B))
  let K := dualScaleLoss α
  have hK : 0 < K := dualScaleLoss_pos hα.le
  let C := max (max B T) (max (⌈4*α⌉₊+1) ((2048*K)^64))
  obtain ⟨u, v, r, hu, hv, hvu, huv, rfl, hr, hlo, hhi, hrows⟩ :=
    exists_polynomial_beatty_arc_scale_data hα hI C
  have hu0 : 0 < u := (Nat.zero_le C).trans_lt hu
  have hTu : T ≤ u := (le_max_right B T).trans ((le_max_left _ _).trans hu.le)
  obtain ⟨hdiag, hcut⟩ := hT u hTu
  have hαu : 4*α ≤ u := (Nat.le_ceil _).trans (by
    exact_mod_cast (Nat.le_succ ⌈4*α⌉₊).trans
      ((le_max_left (⌈4*α⌉₊+1) ((2048*K)^64)).trans ((le_max_right (max B T) _).trans hu.le)))
  have hKu : (2048*K)^64 ≤ u :=
    (le_max_right (⌈4*α⌉₊+1) _).trans ((le_max_right (max B T) _).trans hu.le)
  have hKv : 2048*K ≤ root64 u := (le_root64_iff _ _).mpr hKu
  have hq : 2*α ≤ r.den := by
    have hu4 : (u : ℝ) ≤ (u : ℝ)^4 := by exact_mod_cast Nat.le_self_pow (by norm_num : 4 ≠ 0) u
    have hloR : (u : ℝ)^4 ≤ r.den := by exact_mod_cast hlo
    linarith only [hα, hαu, hu4, hloR]
  obtain ⟨s, hslo, hshi, hs⟩ := inverse_good_approximant hα.le r hr hq (Nat.le_ceil α)
  change r.den ≤ K*s.den at hslo
  change s.den ≤ K*r.den at hshi
  have hslo' : u^4 ≤ K*s.den := hlo.trans hslo
  have hshi' : s.den ≤ 16*K*u^4 := by
    have hh := hshi.trans (Nat.mul_le_mul_left K hhi)
    nlinarith only [hh]
  obtain ⟨a, q, hq0, haq, hqlo, hqhi, hqa, hNsq⟩ := inverse_diagonal_data hα.le r hr hu0 hαu hlo hhi
  refine ⟨u, (le_max_left B T).trans_lt ((le_max_left _ _).trans_lt hu), hcut,
    hαu, hKv, hrows, ?_, ?_, hdiag a q hq0 haq hqlo hqhi hqa hNsq⟩
  · intro e he hev X hX
    exact input_divisor_row_discrepancy (by linarith : 0 ≤ α) s hs hK hKv hvu hslo' hshi' he hev hX
  · intro d e hd he hev X hX
    apply reciprocal_scale_divisor_prefix_bound hα.le r hr hu0
      (show 0 < root64 u by omega) hαu hlo hhi _ hd he hev
    have hα0 : 0 < α := by linarith
    have hh : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
    have hXR : (X : ℝ) ≤ scaleCutoff α u := Nat.cast_le.mpr hX
    have hh' := (le_div_iff₀ hα0).mp (hXR.trans hh)
    nlinarith only [hh']

#print axioms inverse_diagonal_data
#print axioms exists_two_sided_scale_small_diagonal

end Erdos972CommonAsymmetricDiagonal
