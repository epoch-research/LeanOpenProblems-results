import Submission.DualPrimeRows
import Submission.OrdinaryRotationMean

/-! Prime-input rows for every residue class of the floor output. The
translation is uniform, and all rows use one fixed rational approximant. -/
namespace Erdos972ResiduePrimeRows

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972RationalRotationCount
open Erdos972WeightedPrimeRotation Erdos972ScaledPrimeRows Erdos972DualPrimeRows
open Erdos972OrdinaryRotationMean

set_option maxHeartbeats 1500000

lemma floor_mod_eq_floor_fract {x : ℝ} (hx : 0 ≤ x) {e : ℕ} (he : 0 < e) :
    ⌊x⌋₊ % e = ⌊(e : ℝ)*Int.fract (x/e)⌋₊ := by
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have hf : Int.fract (x/e) = x/e-(⌊x⌋₊/e : ℕ) := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor (div_nonneg hx heR.le),
      Nat.floor_div_natCast, Int.cast_natCast]
  have hd : (e : ℝ)*(⌊x⌋₊/e : ℕ)+(⌊x⌋₊%e : ℕ) = ⌊x⌋₊ := by
    exact_mod_cast Nat.div_add_mod ⌊x⌋₊ e
  symm
  apply (Nat.floor_eq_iff (mul_nonneg heR.le (Int.fract_nonneg _))).mpr
  rw [hf]
  have hmul : (e : ℝ)*(x/e-(⌊x⌋₊/e : ℕ)) = x-e*(⌊x⌋₊/e : ℕ) := by field_simp
  rw [hmul]
  constructor <;> linarith only [hd, Nat.floor_le hx, Nat.lt_floor_add_one x]

lemma floor_mod_eq_iff_arc {x : ℝ} (hx : 0 ≤ x) {e : ℕ} (he : 0 < e) (j : ℕ) :
    ⌊x⌋₊%e = j ↔ (j : ℝ)/e ≤ Int.fract (x/e) ∧ Int.fract (x/e) < ((j : ℝ)+1)/e := by
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr he
  rw [floor_mod_eq_floor_fract hx he, Nat.floor_eq_iff (mul_nonneg heR.le (Int.fract_nonneg _))]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨(div_le_iff₀ heR).mpr (by nlinarith only [hlo]),
      (lt_div_iff₀ heR).mpr (by nlinarith only [hhi])⟩
  · rintro ⟨hlo, hhi⟩
    have hl := (div_le_iff₀ heR).mp hlo
    have hh := (lt_div_iff₀ heR).mp hhi
    constructor <;> nlinarith only [hl, hh]

lemma fract_sub_arc {x a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Int.fract (x-a) < b-a ↔ a ≤ Int.fract x ∧ Int.fract x < b := by
  have he : Int.fract (x-a) = Int.fract (Int.fract x-a) := by
    rw [show x-a = (Int.fract x-a)+(⌊x⌋ : ℝ) by linarith only [Int.fract_add_floor x],
      Int.fract_add_intCast]
  rw [he]
  by_cases hax : a ≤ Int.fract x
  · rw [Int.fract_eq_self.mpr ⟨sub_nonneg.mpr hax, by linarith only [Int.fract_lt_one x, ha]⟩]
    constructor
    · intro h; exact ⟨hax, by linarith only [h]⟩
    · intro h; linarith only [h.2]
  · have he' : Int.fract (Int.fract x-a) = Int.fract x-a+1 := by
      rw [← Int.fract_add_one]
      apply Int.fract_eq_self.mpr
      constructor <;> linarith only [hax, Int.fract_nonneg x, hab, hb]
    rw [he']
    constructor
    · intro h; exfalso; linarith only [h, Int.fract_nonneg x, hb]
    · intro h; exact (hax h.1).elim

noncomputable def inputResidueRow (α : ℝ) (e j N : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 N).filter (fun n => floorMul α n % e = j), vonMangoldt n

lemma inputResidueRow_zero (α : ℝ) (e N : ℕ) :
    inputResidueRow α e 0 N = inputDivisorRow α e N := by
  simp only [inputResidueRow, inputDivisorRow, Nat.dvd_iff_mod_eq_zero]

lemma inputResidueRow_arc {α : ℝ} (hα : 0 ≤ α) {e j : ℕ} (he : 1 < e)
    (hj : j < e) (N : ℕ) :
    inputResidueRow α e j N = mangoldtArcSum (α/e)
      ((1-1/(e : ℝ))/2-(j : ℝ)/e) ((1-1/(e : ℝ))/2)
      ((1-1/(e : ℝ))/2+1/e) N := by
  have heR : (1 : ℝ) < e := by exact_mod_cast he
  have he0 : (0 : ℝ) < e := by linarith only [heR]
  have hw : (0 : ℝ) < 1/e := by positivity
  have hw1 : 1/(e : ℝ) < 1 := (div_lt_one he0).mpr heR
  have hjR : (j : ℝ)+1 ≤ e := by exact_mod_cast hj
  have hp (n : ℕ) : floorMul α n % e = j ↔
      (1-1/(e : ℝ))/2 ≤ Int.fract ((α/e)*n+((1-1/(e : ℝ))/2-(j : ℝ)/e)) ∧
      Int.fract ((α/e)*n+((1-1/(e : ℝ))/2-(j : ℝ)/e)) < (1-1/(e : ℝ))/2+1/e := by
    rw [show (α/e)*n+((1-1/(e : ℝ))/2-(j : ℝ)/e) =
      (α*n/e-(j : ℝ)/e)+(1-1/(e : ℝ))/2 by ring,
      fract_shift_arc (by linarith only [hw1]) (by linarith only [hw1]) hw.le,
      show 1/(e : ℝ) = ((j : ℝ)+1)/e-(j : ℝ)/e by ring,
      fract_sub_arc (by positivity) (by apply div_le_div_of_nonneg_right _ he0.le; linarith)
        ((div_le_one he0).mpr hjR)]
    exact floor_mod_eq_iff_arc (by positivity) (by omega) j
  simp only [inputResidueRow, mangoldtArcSum, sum_filter, hp]

/-- Every residue, not only residue zero, has the same one-prime discrepancy
bound at this common rational scale. -/
theorem input_residue_row_discrepancy {α : ℝ} (hα : 0 ≤ α)
    (r : ℚ) (hr : |α-r| ≤ 1/(r.den : ℝ)^2)
    {K u v : ℕ} (hK : 0 < K) (hv : 2048*K ≤ v) (hvu : v^64 ≤ u)
    (hlo : u^4 ≤ K*r.den) (hhi : r.den ≤ 16*K*u^4)
    {e j X : ℕ} (he : 0 < e) (hev : e ≤ v) (hj : j < e) (hX : X ≤ u^6) :
    |inputResidueRow α e j X-Chebyshev.psi X/e| ≤ scaledRowError K u v := by
  by_cases he1 : e = 1
  · have hj0 : j = 0 := by omega
    subst e; subst j
    rw [inputResidueRow_zero]
    exact input_divisor_row_discrepancy hα r hr hK hv hvu hlo hhi (by norm_num) hev hX
  have he2 : 1 < e := by omega
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he2
  have he0 : (0 : ℝ) < e := by positivity
  have hv0 : 0 < v := he.trans_le hev
  have hvR : (2 : ℝ) ≤ v := heR.trans (Nat.cast_le.mpr hev)
  have hw : 1/(e : ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) heR
  have hquarter : 1/(v : ℝ)^3 ≤ 1/4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith only [hvR, mul_self_nonneg ((v : ℝ)-2),
      mul_nonneg (show 0 ≤ (v : ℝ)-2 by linarith only [hvR]) (sq_nonneg (v : ℝ))]
  have hh := scaled_arc_prefix_bound hα r hr K u v v hK hv0 le_rfl hv hvu hlo hhi
    ((1-1/(e : ℝ))/2) ((1-1/(e : ℝ))/2+1/e) ((1-1/(e : ℝ))/2-(j : ℝ)/e)
    (by linarith only [show 0 ≤ 1/(e : ℝ) by positivity])
    (by linarith only [hquarter, hw]) (by linarith only [hquarter, hw]) e X he hev hX
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num,
    Erdos972BeattyRowScales.mangoldtArcSum_nat_add, add_sub_cancel_left] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [← inputResidueRow_arc hα he2 hj X] at hh
  simpa only [one_div_mul_eq_div] using hh

#print axioms input_residue_row_discrepancy
end Erdos972ResiduePrimeRows
