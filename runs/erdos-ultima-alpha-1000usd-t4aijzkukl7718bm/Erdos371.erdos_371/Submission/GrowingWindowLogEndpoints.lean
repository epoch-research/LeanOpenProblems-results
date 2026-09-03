import Submission.GrowingWindowLargestPrimeHalf

/-! Endpoint-ratio form of the growing harmonic-window result. The difference
between harmonic mass and the logarithm of the endpoint ratio is at most one. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma positiveRawSum_one (T : ℕ) : positiveRawSum T (fun _ => 1) = (harmonic T : ℝ) := by
  simp [positiveRawSum,harmonic_eq_sum_Icc,one_div]

lemma shiftedHarmonicMass_eq_harmonic_sub (A N : ℕ) :
    shiftedHarmonicMass A N = (harmonic (A+N+1) : ℝ)-harmonic A := by
  rw [shiftedHarmonicMass,shiftedHarmonicRaw_eq_sub,positiveRawSum_one,positiveRawSum_one]

lemma shiftedHarmonicMass_log_ratio_bound (A N : ℕ) :
    |shiftedHarmonicMass A N-Real.log ((A+N+2 : ℝ)/(A+1))| ≤ 1 := by
  have hup := harmonic_le_one_add_log (A+N+1)
  have hlo := log_add_one_le_harmonic (A+N+1)
  have hAlow := log_add_one_le_harmonic A
  have hAup : (harmonic A : ℝ) ≤ 1+Real.log (A+1 : ℝ) := by
    by_cases hA : A=0
    · subst A; norm_num
    · have hpos : (0 : ℝ) < A := by exact_mod_cast (Nat.pos_of_ne_zero hA)
      exact (harmonic_le_one_add_log A).trans
        (add_le_add le_rfl (Real.log_le_log hpos (by linarith)))
  have hlog : Real.log (A+N+1 : ℝ) ≤ Real.log (A+N+2 : ℝ) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [shiftedHarmonicMass_eq_harmonic_sub,
    Real.log_div (by positivity : (A+N+2 : ℝ) ≠ 0) (by positivity : (A+1 : ℝ) ≠ 0)]
  simp only [Nat.cast_add,Nat.cast_one] at hup hlo hAlow
  have hlo' : Real.log (A+N+2 : ℝ) ≤ (harmonic (A+N+1) : ℝ) := by
    convert hlo using 1
    congr 1
    ring
  rw [abs_le]
  constructor <;> linarith

lemma shiftedHarmonicMass_tendsto_of_ratio (A M : ℕ → ℕ)
    (hR : Tendsto (fun j => (A j+M j+2 : ℝ)/(A j+1)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop := by
  have ht := (Real.tendsto_log_atTop.comp hR).atTop_add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)))
  apply tendsto_atTop_mono _ ht
  intro j
  have hb := (abs_le.mp (shiftedHarmonicMass_log_ratio_bound (A j) (M j))).1
  dsimp only [Function.comp_apply]
  linarith

end Erdos371.FiniteInformation
namespace Erdos371
open Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

/-- The actual harmonic rise proportion is one half whenever the ratio of
the interval endpoints tends to infinity, however slowly. -/
theorem largest_prime_rises_growing_ratio_half (A M : ℕ → ℕ)
    (hR : Tendsto (fun j => (A j+M j+2 : ℝ)/(A j+1)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun n => if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then (1 : ℝ) else 0)) atTop (𝓝 (1/2)) :=
  largest_prime_rises_growing_harmonic_half A M (shiftedHarmonicMass_tendsto_of_ratio A M hR)

#print axioms largest_prime_rises_growing_ratio_half
end Erdos371
