import Submission.RationalBandFourierScales
import Submission.AsymmetricDiagonalBudget
import Submission.LeastFactorCutoff

/-! Finite sums over a growing grid of rational Fourier bands. -/
namespace Erdos972GrowingRationalGrid

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972RationalBandFourierBounds
open Erdos972DivisorMeanRecenter Erdos972MobiusPartialSums
open Erdos972ResiduePrimeRows Erdos972ResidueDivisorCounts
open Erdos972PolynomialRowScales Erdos972PrimeRotation Erdos972GrowingTypeI
open Erdos972LeastFactorCutoff

set_option maxHeartbeats 2000000
attribute [local irreducible] root64

abbrev GridIndex := ℕ × ℕ × ℤ

def gridIndices (B : ℕ) : Finset GridIndex :=
  ((Ioc 0 B) ×ˢ ((Ioc 0 B) ×ˢ (Icc (-(B : ℤ)) B))).filter fun t => t.2.1 < t.1

lemma mem_gridIndices {B : ℕ} {t : GridIndex} (ht : t ∈ gridIndices B) :
    0 < t.1 ∧ t.1 ≤ B ∧ 0 < t.2.1 ∧ t.2.1 < t.1 ∧ |(t.2.2 : ℝ)| ≤ B := by
  obtain ⟨ht, ha⟩ := mem_filter.mp ht
  obtain ⟨hq, ht⟩ := mem_product.mp ht
  obtain ⟨hn, hj⟩ := mem_product.mp ht
  obtain ⟨hj1, hj2⟩ := mem_Icc.mp hj
  refine ⟨(mem_Ioc.mp hq).1, (mem_Ioc.mp hq).2, (mem_Ioc.mp hn).1, ha, ?_⟩
  rw [abs_le]
  constructor <;> exact_mod_cast (by assumption)

lemma gridIndices_card (B : ℕ) : (gridIndices B).card ≤ B^2*(2*B+1) := by
  have hI : (Icc (-(B : ℤ)) B).card = 2*B+1 := by
    rw [Int.card_Icc]
    omega
  have hh := card_filter_le (s := (Ioc 0 B) ×ˢ ((Ioc 0 B) ×ˢ (Icc (-(B : ℤ)) B)))
    (p := fun t : GridIndex => t.2.1 < t.1)
  simp only [card_product, Nat.card_Ioc, Nat.sub_zero, hI] at hh
  exact hh.trans_eq (by ring)

lemma gridIndices_card_real {B : ℕ} (hB : 0 < B) :
    ((gridIndices B).card : ℝ) ≤ 3*(B : ℝ)^3 := by
  have hh : ((gridIndices B).card : ℝ) ≤ (B : ℝ)^2*(2*B+1) := by exact_mod_cast gridIndices_card B
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hm := mul_le_mul_of_nonneg_left (show 2*(B : ℝ)+1 ≤ 3*B by linarith only [hBR]) (sq_nonneg (B : ℝ))
  nlinarith only [hh, hm]

noncomputable def gridFrequency (J : ℕ) (t : GridIndex) : ℤ :=
  rationalFrequency J t.1 t.2.1 t.2.2

noncomputable def rationalGrid (J : ℕ) [NeZero J] (B : ℕ) : Finset (ZMod J) :=
  (gridIndices B).image fun t => (gridFrequency J t : ZMod J)

lemma rationalGrid_card (J : ℕ) [NeZero J] (B : ℕ) :
    (rationalGrid J B).card ≤ B^2*(2*B+1) :=
  (card_image_le).trans (gridIndices_card B)

lemma grid_numerator_nonzero {q a : ℕ} (ha : 0 < a) (haq : a < q) :
    ((a : ℤ) : ZMod q) ≠ 0 := by
  simp only [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
  intro h
  exact (not_le.mpr haq) (Nat.le_of_dvd ha h)

/-- Absolute mode sums are controlled, so overlapping bands and repeated
rational representations cannot cause an omitted contribution. -/
theorem rationalGrid_norm_sum_bound {α : ℝ} (hα : 1 ≤ α) {W v N Q : ℕ}
    (hW : 0 < W) (hWv : W*W ≤ v) (hvN : v ≤ N) (hQ : 0 < Q)
    {L Ep Bd : ℝ} (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (hlogM : Real.log (floorMul α N) ≤ L-1)
    (hm : |reciprocalMoebius W| ≤ 1) (hBd : 0 ≤ Bd)
    (hprime : ∀ q ∈ Ioc 0 Q, ∀ X ≤ N, ∀ j < q,
      |inputResidueRow α q j X-Chebyshev.psi X/q| ≤ Ep)
    (hdiv : ∀ q ∈ Ioc 0 Q, ∀ X ≤ N, ∀ d ∈ Ioc 0 v, ∀ j < q,
      |((residueDivisorPairs α X d q j).card : ℝ)-(X : ℝ)/(d*q)| ≤ Bd) :
    (∑ k ∈ rationalGrid (floorMul α N+1) Q,
      ‖covarianceFourierTerm α N (fun n => meanCenteredTypeII W W n)
          (fun n => meanCenteredTypeII W W n) k/((floorMul α N+1 : ℕ) : ℂ)‖) ≤
      15*(1+4*Real.pi)*(Q : ℝ)^5*(v : ℝ)*L^2*(Ep+40*(v : ℝ)*L^2*(Bd+1)) := by
  have hEp : 0 ≤ Ep := by
    have hh := hprime 1 (mem_Ioc.mpr ⟨by norm_num, hQ⟩) 0 (Nat.zero_le N) 0 (by norm_num)
    simpa [inputResidueRow, Chebyshev.psi] using hh
  let J := floorMul α N+1
  let R := fun n => meanCenteredTypeII W W n
  let F := fun k : ZMod J => covarianceFourierTerm α N R R k/(J : ℂ)
  let A := 5*(1+4*Real.pi)*(Q : ℝ)^2*(v : ℝ)*L^2*(Ep+40*(v : ℝ)*L^2*(Bd+1))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hterm (t : GridIndex) (ht : t ∈ gridIndices Q) : ‖F (gridFrequency J t : ZMod J)‖ ≤ A := by
    obtain ⟨hq, hqQ, ha, haq, hjQ⟩ := mem_gridIndices ht
    have hh := rational_fourier_term_bound hα hW hWv hvN hq (t.2.1 : ℤ)
      (grid_numerator_nonzero ha haq) hL hlog hlogM hm hBd
      (hprime t.1 (mem_Ioc.mpr ⟨hq, hqQ⟩)) (hdiv t.1 (mem_Ioc.mpr ⟨hq, hqQ⟩))
      (gridFrequency J t) (rationalFrequency_near J t.1 t.2.1 t.2.2)
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hc : 1+2*Real.pi*(|(t.2.2 : ℝ)|+1) ≤ (1+4*Real.pi)*(Q : ℝ) := by
      have hm' := mul_le_mul_of_nonneg_left hjQ (show 0 ≤ 2*Real.pi by positivity)
      have hQ' := mul_le_mul_of_nonneg_left hQR (show 0 ≤ 2*Real.pi by positivity)
      nlinarith only [hm', hQ', hQR]
    have hqR : (t.1 : ℝ) ≤ Q := Nat.cast_le.mpr hqQ
    have hprod := mul_le_mul hc hqR (Nat.cast_nonneg (α := ℝ) t.1)
      (show 0 ≤ (1+4*Real.pi)*(Q : ℝ) by positivity)
    have hrest : 0 ≤ 5*(v : ℝ)*L^2*(Ep+40*(v : ℝ)*L^2*(Bd+1)) := by positivity
    have hb := mul_le_mul_of_nonneg_right hprod hrest
    dsimp only [F, R, J, A]
    nlinarith only [hh, hb]
  change (∑ k ∈ rationalGrid J Q, ‖F k‖) ≤ _
  apply (sum_image_le_of_nonneg (fun k hk => norm_nonneg (F k))).trans
  apply (sum_le_sum hterm).trans
  rw [sum_const, nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right (gridIndices_card_real hQ) hA).trans_eq (by dsimp only [A]; ring)

/-- A polynomially growing denominator and offset cutoff, rather than a
finite set chosen before taking a limit. -/
def bandCutoff (u : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (root64 u))

lemma bandCutoff_tendsto : Tendsto bandCutoff atTop atTop := by
  exact nat_fourth_root_tendsto.comp root64_tendsto

lemma bandCutoff_bounds {u : ℕ} (hu : 0 < u) :
    0 < bandCutoff u ∧ bandCutoff u^4 ≤ root64 u ∧ bandCutoff u ≤ root64 u := by
  obtain ⟨hB, hB4, _⟩ := fourth_root_bounds (root64_bounds hu).1
  refine ⟨hB, hB4, ?_⟩
  exact (Nat.le_self_pow (by norm_num) _).trans hB4

lemma small_cutoff_le_bandCutoff {u : ℕ} (hu : 0 < u) :
    Erdos972AsymmetricDiagonalBudget.mobiusCutoff u ≤ bandCutoff u := by
  apply (le_fourth_root_iff _ _).mpr
  have hv := (root64_bounds hu).1
  obtain ⟨hB, hB64, _⟩ := root64_bounds hv
  exact (Nat.pow_le_pow_right hB (show 4 ≤ 64 by norm_num)).trans hB64

#print axioms rationalGrid_norm_sum_bound
#print axioms bandCutoff_bounds
end Erdos972GrowingRationalGrid
