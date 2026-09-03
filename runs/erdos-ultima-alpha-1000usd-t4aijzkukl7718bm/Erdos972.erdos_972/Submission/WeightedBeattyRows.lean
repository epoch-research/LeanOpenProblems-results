import Submission.CommonLogCenter
import Submission.PolynomialRowScales

/-! Logarithmically weighted Beatty rows, with an explicit uniform error.
These estimates still contain only one prime variable. -/
namespace Erdos972WeightedBeattyRows

open Finset ArithmeticFunction Classical
open Erdos972ExponentialSum
open Erdos972PrimePowerError Erdos972BeattyRows Erdos972WeightedPrimeRotation
open Erdos972SelfCenteredLog Erdos972CommonLogCenter

set_option maxHeartbeats 1000000

def rowArc (β : ℝ) (q : ℕ) : Prop :=
  rowArcLeft β ≤ Int.fract ((1/β)*q-rowArcLeft β) ∧
    Int.fract ((1/β)*q-rowArcLeft β) < 1-rowArcLeft β

noncomputable def outputRow (β : ℝ) (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ q ∈ (Ioc 0 X).filter (rowArc β), f q

lemma row_image {β : ℝ} (hβ : 1 < β) (hI : Irrational β) (N : ℕ) :
    (Ioc 0 N).image (floorMul β) = (Ioc 0 (floorMul β N)).filter (rowArc β) := by
  classical
  have hb := rowArcLeft_bounds hβ
  ext q
  rw [mem_image, mem_filter, mem_Ioc]
  by_cases hq : 0 < q
  · unfold rowArc
    rw [fract_sub_center hb.1 hb.2]
    have he : 2*rowArcLeft β = 1-1/β := by unfold rowArcLeft; ring
    rw [he, one_div_mul_eq_div, floorMul_image_iff hβ hI N q hq]
    tauto
  · constructor
    · rintro ⟨n, hn, he⟩
      exact (hq (he ▸ floorMul_pos hβ.le (mem_Ioc.mp hn).1)).elim
    · intro hh
      exact (hq hh.1.1).elim

lemma weightedRow_eq_outputRow {β : ℝ} (hβ : 1 < β) (hI : Irrational β)
    (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f (floorMul β n)) = outputRow β f (floorMul β N) := by
  classical
  rw [← sum_image (fun n hn m hm he => (floorMul_strictMono hβ.le).injective he), row_image hβ hI]
  rfl

lemma outputRow_mangoldt (β : ℝ) (X : ℕ) :
    outputRow β (fun q => vonMangoldt q) X =
      mangoldtArcSum (1/β) (-rowArcLeft β) (rowArcLeft β) (1-rowArcLeft β) X := by
  unfold outputRow mangoldtArcSum
  congr 1
  ext q
  simp only [mem_filter, rowArc, sub_eq_add_neg]

lemma output_log_discrepancy (β E : ℝ) (Q : ℕ)
    (hE : ∀ X ≤ Q, |outputRow β (fun q => vonMangoldt q) X-(1/β)*Chebyshev.psi X| ≤ E) :
    |outputRow β (fun q => Real.log q*vonMangoldt q) Q-
      (1/β)*logRow (fun q => vonMangoldt q) Q| ≤ 2*Real.log Q*E := by
  classical
  have hzero : (1/β)*Chebyshev.psi (0 : ℕ) = 0 := by simp [Chebyshev.psi]
  have hh := logRow_prefix_approx (fun q => if rowArc β q then vonMangoldt q else 0)
    (fun X => (1/β)*Chebyshev.psi X) hzero Q E (by
      intro X hX
      simpa only [outputRow, sum_filter] using hE X hX)
  have hrow : logRow (fun q => if rowArc β q then vonMangoldt q else 0) Q =
      outputRow β (fun q => Real.log q*vonMangoldt q) Q := by
    simp only [logRow, outputRow, sum_filter, mul_ite, mul_zero]
  have hinc : logIncrement (fun X => (1/β)*Chebyshev.psi X) Q =
      (1/β)*logRow (fun q => vonMangoldt q) Q := by
    rw [← logIncrement_psi]
    simp only [logIncrement, mul_sum]
    apply sum_congr rfl
    intro q hq
    ring
  rwa [hrow, hinc] at hh

lemma log_floorMul_gap {β : ℝ} (hβ : 1 ≤ β) {n : ℕ} (hn : 0 < n) :
    0 ≤ Real.log β+Real.log n-Real.log (floorMul β n) ∧
      Real.log β+Real.log n-Real.log (floorMul β n) ≤ 1/(floorMul β n : ℝ) := by
  have hβ0 : 0 < β := by linarith
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq0 : (0 : ℝ) < floorMul β n := Nat.cast_pos.mpr (floorMul_pos hβ hn)
  have hlo : (floorMul β n : ℝ) ≤ β*n := Nat.floor_le (by positivity)
  have hhi : β*n < (floorMul β n : ℝ)+1 := Nat.lt_floor_add_one _
  rw [← Real.log_mul hβ0.ne' hn0.ne']
  refine ⟨sub_nonneg.mpr (Real.log_le_log hq0 hlo), ?_⟩
  have hh := Real.log_le_sub_one_of_pos (div_pos (mul_pos hβ0 hn0) hq0)
  rw [Real.log_div (mul_pos hβ0 hn0).ne' hq0.ne'] at hh
  apply hh.trans
  apply (le_div_iff₀ hq0).mpr
  have he : (β*n/(floorMul β n : ℝ)-1)*(floorMul β n : ℝ) = β*n-floorMul β n := by field_simp
  rw [he]
  linarith

lemma harmonic_Ioc_bound (Q : ℕ) : (∑ q ∈ Ioc 0 Q, 1/(q : ℝ)) ≤ 1+Real.log Q := by
  have he : (∑ q ∈ Ioc 0 Q, 1/(q : ℝ)) = (harmonic Q : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, one_div, ← Icc_add_one_left_eq_Ioc, Nat.zero_add]
  rw [he]
  exact harmonic_le_one_add_log Q

/-- Replacing the input logarithm by the output logarithm costs only a
squared logarithm, independent of the number of terms in the row. -/
lemma input_output_log_error {β : ℝ} (hβ : 1 ≤ β) (N : ℕ) :
    |logRow (fun n => vonMangoldt (floorMul β n)) N-
      (∑ n ∈ Ioc 0 N, (Real.log (floorMul β n)-Real.log β)*vonMangoldt (floorMul β n))| ≤
        Real.log (floorMul β N)*(1+Real.log (floorMul β N)) := by
  have he : logRow (fun n => vonMangoldt (floorMul β n)) N-
      (∑ n ∈ Ioc 0 N, (Real.log (floorMul β n)-Real.log β)*vonMangoldt (floorMul β n)) =
      ∑ n ∈ Ioc 0 N, (Real.log β+Real.log n-Real.log (floorMul β n))*vonMangoldt (floorMul β n) := by
    unfold logRow
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    ring
  rw [he, abs_of_nonneg (sum_nonneg (fun n hn => mul_nonneg (log_floorMul_gap hβ (mem_Ioc.mp hn).1).1 vonMangoldt_nonneg))]
  classical
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (1/(floorMul β n : ℝ))*Real.log (floorMul β N) := by
      apply sum_le_sum
      intro n hn
      have hlog := vonMangoldt_le_log (n := floorMul β n)
      have hqQ := (floorMul_strictMono hβ).monotone (mem_Ioc.mp hn).2
      apply mul_le_mul (log_floorMul_gap hβ (mem_Ioc.mp hn).1).2
        (hlog.trans (monotone_log_natCast hqQ)) vonMangoldt_nonneg
      positivity
    _ = ∑ q ∈ (Ioc 0 N).image (floorMul β), (1/(q : ℝ))*Real.log (floorMul β N) := by
      rw [sum_image (fun n hn m hm he => (floorMul_strictMono hβ).injective he)]
    _ ≤ ∑ q ∈ Ioc 0 (floorMul β N), (1/(q : ℝ))*Real.log (floorMul β N) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
        exact mem_Ioc.mpr ⟨floorMul_pos hβ (mem_Ioc.mp hn).1,
          (floorMul_strictMono hβ).monotone (mem_Ioc.mp hn).2⟩
      · intro q hq hqn
        positivity [Real.log_natCast_nonneg (floorMul β N)]
    _ = (∑ q ∈ Ioc 0 (floorMul β N), 1/(q : ℝ))*Real.log (floorMul β N) := by rw [sum_mul]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (harmonic_Ioc_bound (floorMul β N))
        (Real.log_natCast_nonneg (floorMul β N))
      nlinarith only [hh]

/-- The main term is indexed by prime outputs. This form makes the main terms
of different input rows align at a common endpoint. -/
theorem logRow_output_approx {β E : ℝ} (hβ : 1 < β) (hI : Irrational β) (N : ℕ)
    (hE : ∀ X ≤ floorMul β N,
      |outputRow β (fun q => vonMangoldt q) X-(1/β)*Chebyshev.psi X| ≤ E) :
    |logRow (fun n => vonMangoldt (floorMul β n)) N-
      (1/β)*(logRow (fun q => vonMangoldt q) (floorMul β N)-
        Real.log β*Chebyshev.psi (floorMul β N))| ≤
      (2*Real.log (floorMul β N)+Real.log β)*E+
        Real.log (floorMul β N)*(1+Real.log (floorMul β N)) := by
  have hlog := output_log_discrepancy β E (floorMul β N) hE
  have hconst := mul_le_mul_of_nonneg_left (hE _ le_rfl) (Real.log_nonneg hβ.le)
  have he : (∑ n ∈ Ioc 0 N, (Real.log (floorMul β n)-Real.log β)*vonMangoldt (floorMul β n)) =
      outputRow β (fun q => Real.log q*vonMangoldt q) (floorMul β N)-
        Real.log β*outputRow β (fun q => vonMangoldt q) (floorMul β N) := by
    rw [weightedRow_eq_outputRow hβ hI (fun q => (Real.log q-Real.log β)*vonMangoldt q)]
    simp only [outputRow, sub_mul, sum_sub_distrib, mul_sum]
  have herr := input_output_log_error hβ.le N
  rw [he] at herr
  let A := outputRow β (fun q => Real.log q*vonMangoldt q) (floorMul β N)-
    (1/β)*logRow (fun q => vonMangoldt q) (floorMul β N)
  let B := Real.log β*(outputRow β (fun q => vonMangoldt q) (floorMul β N)-(1/β)*Chebyshev.psi (floorMul β N))
  have hB : |B| ≤ Real.log β*E := by
    dsimp [B]
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg hβ.le)]
    exact hconst
  have hA : |A| ≤ 2*Real.log (floorMul β N)*E := hlog
  have hsplit : logRow (fun n => vonMangoldt (floorMul β n)) N-
      (1/β)*(logRow (fun q => vonMangoldt q) (floorMul β N)-Real.log β*Chebyshev.psi (floorMul β N)) =
      (logRow (fun n => vonMangoldt (floorMul β n)) N-
        (outputRow β (fun q => Real.log q*vonMangoldt q) (floorMul β N)-
          Real.log β*outputRow β (fun q => vonMangoldt q) (floorMul β N)))+(A-B) := by
    dsimp [A, B]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add herr ((abs_sub _ _).trans (add_le_add hA hB))) |>.trans (by ring_nf; exact le_rfl)

#print axioms logRow_output_approx

end Erdos972WeightedBeattyRows
