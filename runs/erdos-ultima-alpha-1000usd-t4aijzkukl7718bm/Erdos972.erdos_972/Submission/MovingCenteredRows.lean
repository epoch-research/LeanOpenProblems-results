import Submission.RealLogCenter
import Submission.CenteredVaughan

/-! Common-center estimates for moving families of Type-I rows. -/
namespace Erdos972MovingCenteredRows

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972PrimePowerError Erdos972WeightedBeattyRows Erdos972BeattyRows
open Erdos972SelfCenteredLog Erdos972CommonLogCenter Erdos972RealLogCenter
open Erdos972ChebyshevRowMean Erdos972CenteredVaughan Erdos972ExponentialSum
open Erdos972Vaughan Erdos972CorrelationVaughan

set_option maxHeartbeats 1000000

lemma centeredLogRow_eq (a : ℕ → ℝ) (ρ : ℝ) (N : ℕ) :
    centeredLogRow a ρ N = logRow a N-ρ*logMass N := by
  simp only [centeredLogRow, logRow, logMass, mul_sub, sum_sub_distrib, ← sum_mul]
  ring

/-- All logarithmic rows have the same scalar main term, divided by their
multiplier. This is what preserves the signed Möbius sum. -/
theorem common_centered_log_row {β y E : ℝ} (hβ : 1 < β) (hI : Irrational β)
    {L : ℕ} (hL : 0 < L) (hlo : β*L ≤ y) (hhi : y ≤ β*((L : ℝ)+1))
    (hE : ∀ X ≤ floorMul β L,
      |outputRow β (fun q => vonMangoldt q) X-(1/β)*Chebyshev.psi X| ≤ E) :
    |centeredLogRow (fun n => vonMangoldt (floorMul β n)) (Chebyshev.psi y/y) L-
      commonLogCenter y/β| ≤ 3*Real.log y*E+25*(1+Real.log y)^2 := by
  have hβ0 : 0 < β := by linarith
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hβy : β ≤ y := (le_mul_of_one_le_right hβ0.le hLR).trans hlo
  have hy : 1 ≤ y := hβ.le.trans hβy
  have hlog := Real.log_nonneg hy
  have hlogβ : Real.log β ≤ Real.log y := Real.log_le_log hβ0 hβy
  have hq : (0 : ℝ) < floorMul β L := Nat.cast_pos.mpr (floorMul_pos hβ.le hL)
  have hqlog : Real.log (floorMul β L) ≤ Real.log y := Real.log_le_log hq
    ((Nat.floor_le (show 0 ≤ β*L by positivity)).trans hlo)
  have hE0 : 0 ≤ E := by
    simpa only [outputRow, Ioc_self, filter_empty, sum_empty, Chebyshev.psi,
      Nat.floor_natCast, mul_zero, sub_self, abs_zero] using hE 0 (Nat.zero_le _)
  have hrow := logRow_output_approx hβ hI L hE
  have hend := log_main_endpoint_bound hβ.le hL hlo hhi
  have hpsi : Chebyshev.psi (floorMul β L) = Chebyshev.psi (β*L) := psi_floor _
  rw [hpsi] at hrow
  have he : centeredLogRow (fun n => vonMangoldt (floorMul β n)) (Chebyshev.psi y/y) L-commonLogCenter y/β =
      (logRow (fun n => vonMangoldt (floorMul β n)) L-
        (1/β)*(logRow (fun q => vonMangoldt q) (floorMul β L)-Real.log β*Chebyshev.psi (β*L)))+
      ((1/β)*(logRow (fun q => vonMangoldt q) ⌊β*L⌋₊-Real.log β*Chebyshev.psi (β*L))-
        (Chebyshev.psi y/y)*logMass L-commonLogCenter y/β) := by
    rw [centeredLogRow_eq]
    dsimp only [floorMul]
    ring
  rw [he]
  apply ((abs_add_le _ _).trans (add_le_add hrow hend)).trans
  have hlogQ := Real.log_natCast_nonneg (floorMul β L)
  have hprod : Real.log (floorMul β L)*(1+Real.log (floorMul β L)) ≤ (1+Real.log y)^2 := by
    nlinarith only [hlogQ, hqlog, hlog, sq_nonneg (Real.log y-Real.log (floorMul β L)),
      mul_nonneg (sub_nonneg.mpr hqlog) hlogQ]
  have hc := mul_le_mul_of_nonneg_right (show 2*Real.log (floorMul β L)+Real.log β ≤ 3*Real.log y by linarith only [hqlog, hlogβ]) hE0
  linarith only [hc, hprod]

lemma common_centered_row {β y E : ℝ} (hβ : 1 < β) (hI : Irrational β) (hy : 1 ≤ y)
    (L : ℕ) (hlo : β*L ≤ y) (hhi : y ≤ β*((L : ℝ)+1))
    (hE : |outputRow β (fun q => vonMangoldt q) (floorMul β L)-
      (1/β)*Chebyshev.psi (floorMul β L)| ≤ E) :
    |∑ n ∈ Ioc 0 L, (vonMangoldt (floorMul β n)-Chebyshev.psi y/y)| ≤ E+2*Real.log y+7 := by
  have he : (∑ n ∈ Ioc 0 L, (vonMangoldt (floorMul β n)-Chebyshev.psi y/y)) =
      (outputRow β (fun q => vonMangoldt q) (floorMul β L)-(1/β)*Chebyshev.psi (floorMul β L))+
        (rowMean β L-(Chebyshev.psi y/y)*L) := by
    rw [sum_sub_distrib, weightedRow_eq_outputRow hβ hI (fun q => vonMangoldt q)]
    simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, rowMean, psi_floor, floorMul]
    ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add hE (row_endpoint_bound hβ.le hy L hlo hhi))).trans_eq (by ring)

lemma common_row_geometry {α : ℝ} (hα : 1 < α) {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    1 < α*m ∧ 0 < N/m ∧ (α*m)*(N/m : ℕ) ≤ α*N ∧
      α*N ≤ (α*m)*((N/m : ℕ)+1) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα0 : 0 < α := by linarith
  refine ⟨by nlinarith only [hα, hmR], Nat.div_pos hmN hm, ?_, ?_⟩
  · have hh : (m : ℝ)*(N/m : ℕ) ≤ N := by exact_mod_cast Nat.mul_div_le N m
    nlinarith only [mul_le_mul_of_nonneg_left hh hα0.le]
  · have hh : (N : ℝ) ≤ m*((N/m : ℕ)+1) := by exact_mod_cast (Nat.lt_mul_div_succ N hm).le
    nlinarith only [mul_le_mul_of_nonneg_left hh hα0.le]

/-- The first Type-I sum has a uniformly bounded signed main coefficient. -/
lemma first_common_bound {α R : ℝ} (hα : 0 < α) {U N : ℕ} (hUN : U ≤ N)
    (hrows : ∀ m ∈ Ioc 0 U,
      |centeredLogRow (fun n => vonMangoldt (floorMul (α*m) n)) (commonMean α N) (N/m)-
        commonLogCenter (α*N)/(α*m)| ≤ R) :
    |first α (commonMean α N) U N| ≤ (U : ℝ)*R+2*|commonLogCenter (α*N)|/α := by
  let D := commonLogCenter (α*N)
  let M := ∑ m ∈ Ioc 0 U, (μ m : ℝ)/m
  have he : first α (commonMean α N) U N-(D/α)*M =
      ∑ m ∈ Ioc 0 U, (μ m : ℝ)*
        (centeredLogRow (fun n => vonMangoldt (floorMul (α*m) n)) (commonMean α N) (N/m)-D/(α*m)) := by
    unfold first M
    rw [min_eq_left hUN, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m hm
    simp only [centeredOutput_row, centeredLogRow, mul_sub, div_mul_eq_div_div]
    ring
  have herr : |first α (commonMean α N) U N-(D/α)*M| ≤ (U : ℝ)*R := by
    rw [he]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ m ∈ Ioc 0 U, R := by
        apply sum_le_sum
        intro m hm
        have hμ : |(μ m : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := m)
        rw [abs_mul]
        exact (mul_le_mul hμ (hrows m hm) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by simp
  have hmain : |(D/α)*M| ≤ 2*|D|/α := by
    rw [abs_mul, abs_div, abs_of_nonneg hα.le]
    have hh := mul_le_mul_of_nonneg_left (reciprocal_moebius_sum_bound U) (show 0 ≤ |D|/α by positivity)
    exact hh.trans_eq (by ring)
  have hh := abs_sub_le (first α (commonMean α N) U N) ((D/α)*M) 0
  simp only [sub_zero] at hh
  exact hh.trans (add_le_add herr hmain)

lemma second_uniform_bound {α ρ R : ℝ} (hR : 0 ≤ R) (U V N : ℕ)
    (hrows : ∀ m ∈ Ioc 0 (U*V),
      |∑ n ∈ Ioc 0 (N/m), (vonMangoldt (floorMul (α*m) n)-ρ)| ≤ R) :
    |second α ρ U V N| ≤ (U*V : ℕ)*Real.log (U*V : ℕ)*R := by
  unfold second
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ m ∈ Ioc 0 (min (U*V) N), Real.log (U*V : ℕ)*R := by
      apply sum_le_sum
      intro m hm
      have hmUV : m ∈ Ioc 0 (U*V) := mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2.trans (min_le_left _ _)⟩
      rw [abs_mul]
      simp only [centeredOutput_row]
      exact mul_le_mul ((abs_typeI_coefficient_le_log U V m).trans
        (monotone_log_natCast (mem_Ioc.mp hmUV).2)) (hrows m hmUV) (abs_nonneg _) (Real.log_natCast_nonneg _)
    _ = (min (U*V) N : ℕ)*(Real.log (U*V : ℕ)*R) := by simp
    _ ≤ _ := by
      have hh : ((min (U*V) N : ℕ) : ℝ) ≤ (U*V : ℕ) := Nat.cast_le.mpr (min_le_left _ _)
      nlinarith only [mul_le_mul_of_nonneg_right hh (mul_nonneg (Real.log_natCast_nonneg (U*V)) hR)]

#print axioms common_centered_log_row
#print axioms first_common_bound

end Erdos972MovingCenteredRows
