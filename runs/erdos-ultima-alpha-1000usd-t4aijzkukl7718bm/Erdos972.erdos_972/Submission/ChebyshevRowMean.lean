import Submission.SelfCenteredLog
import Submission.ChebyshevPNT

/-! Chebyshev centers for Beatty rows, and uniform control of the mismatch
between a row endpoint and the common correlation endpoint. -/
namespace Erdos972ChebyshevRowMean

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SelfCenteredLog Erdos972ChebyshevPNT

noncomputable def rowMean (β : ℝ) (N : ℕ) : ℝ := Chebyshev.psi (β*N)/β
noncomputable def commonMean (α : ℝ) (N : ℕ) : ℝ := Chebyshev.psi (α*N)/(α*N)

lemma rowMean_zero (β : ℝ) : rowMean β 0 = 0 := by
  simp only [rowMean, Nat.cast_zero, mul_zero, Chebyshev.psi, Nat.floor_zero, Ioc_self, sum_empty, zero_div]

lemma rowMean_div_tendsto {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun N : ℕ => rowMean β N/N) atTop (𝓝 1) := by
  have hh := psi_div_self_tendsto.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hβ)
  simpa only [rowMean, div_div] using hh

lemma commonMean_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (commonMean α) atTop (𝓝 1) :=
  psi_div_self_tendsto.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hα)

lemma selfCenteredRowMean_tendsto {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun N : ℕ => selfCenteredLog (rowMean β) N/N) atTop (𝓝 0) :=
  selfCenteredLog_div_tendsto (rowMean β) (rowMean_zero β) (rowMean_div_tendsto hβ)

lemma psi_le_seven_mul {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x ≤ 7*x := by
  have hh := Chebyshev.psi_le_const_mul_self hx
  have hlog : Real.log 4 ≤ 3 := by
    simpa only [show (4:ℝ)-1=3 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  nlinarith

lemma psi_ratio_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ Chebyshev.psi x/x ∧ Chebyshev.psi x/x ≤ 7 := by
  exact ⟨div_nonneg (Chebyshev.psi_nonneg _) hx.le, (div_le_iff₀ hx).mpr (psi_le_seven_mul hx.le)⟩

lemma psi_interval_upper {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    Chebyshev.psi y-Chebyshev.psi x ≤ (y-x+1)*Real.log y := by
  have hf : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have he : Chebyshev.psi y-Chebyshev.psi x = ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, vonMangoldt n := by
    have hh := sum_Ioc_consecutive (fun n => (vonMangoldt n : ℝ)) (Nat.zero_le ⌊x⌋₊) hf
    simp only [Chebyshev.psi]
    linarith
  have hcard : ((Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ) ≤ y-x+1 := by
    rw [Nat.card_Ioc, Nat.cast_sub hf]
    linarith [Nat.floor_le (hx.trans hxy), Nat.lt_floor_add_one x]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, Real.log y := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hnx, hny⟩ := mem_Ioc.mp hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hnx)
      exact vonMangoldt_le_log.trans (Real.log_le_log hn0 ((Nat.cast_le.mpr hny).trans (Nat.floor_le (hx.trans hxy))))
    _ = ((Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ)*Real.log y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hy)

/-- Centering a row at a nearby common endpoint costs only a logarithmic error,
uniformly in the row multiplier. -/
lemma row_endpoint_bound {β y : ℝ} (hβ : 1 ≤ β) (hy : 1 ≤ y) (L : ℕ)
    (hlo : β*L ≤ y) (hhi : y ≤ β*((L : ℝ)+1)) :
    |rowMean β L-(Chebyshev.psi y/y)*L| ≤ 2*Real.log y+7 := by
  have hβ0 : 0 < β := by linarith
  have hy0 : 0 < y := by linarith
  have hr := psi_ratio_bounds hy0
  have hlog := Real.log_nonneg hy
  let A := (Chebyshev.psi y-Chebyshev.psi (β*L))/β
  let B := (Chebyshev.psi y/y)*(y/β-L)
  have hA0 : 0 ≤ A := div_nonneg (sub_nonneg.mpr (Chebyshev.psi_mono hlo)) hβ0.le
  have hB0 : 0 ≤ B := by
    apply mul_nonneg hr.1
    exact sub_nonneg.mpr ((le_div_iff₀ hβ0).mpr (by nlinarith))
  have hA : A ≤ 2*Real.log y := by
    have hh := psi_interval_upper (show 0 ≤ β*L by positivity) hlo hy
    have hdelta : y-β*L+1 ≤ 2*β := by nlinarith
    apply (div_le_iff₀ hβ0).mpr
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hdelta hlog])
  have hB : B ≤ 7 := by
    have hh : y/β-L ≤ 1 := by
      have hdiv : y/β ≤ (L : ℝ)+1 := (div_le_iff₀ hβ0).mpr (by nlinarith)
      linarith
    calc
      _ ≤ (Chebyshev.psi y/y)*1 := mul_le_mul_of_nonneg_left hh hr.1
      _ ≤ 7 := by simpa using hr.2
  have he : rowMean β L-(Chebyshev.psi y/y)*L = B-A := by
    dsimp [rowMean, A, B]
    field_simp
    ring
  rw [he]
  exact (abs_sub B A).trans (by rw [abs_of_nonneg hB0, abs_of_nonneg hA0]; linarith)

lemma common_row_endpoint_bound {α : ℝ} (hα : 1 ≤ α) {m N : ℕ} (hm : 0 < m) (hN : 0 < N) :
    |rowMean (α*m) (N/m)-commonMean α N*(N/m : ℕ)| ≤ 2*Real.log (α*N)+7 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hβ : 1 ≤ α*m := by nlinarith
  apply row_endpoint_bound hβ (show 1 ≤ α*N by nlinarith) (N/m)
  · have hh : ((N/m : ℕ) : ℝ)*m ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
    nlinarith
  · have hh : N < m*(N/m+1) := Nat.lt_mul_div_succ N hm
    have hhR : (N : ℝ) ≤ m*(((N/m : ℕ) : ℝ)+1) := by exact_mod_cast hh.le
    nlinarith

#print axioms selfCenteredRowMean_tendsto
#print axioms common_row_endpoint_bound

end Erdos972ChebyshevRowMean
