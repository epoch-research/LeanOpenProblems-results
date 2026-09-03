import Submission.HarmonicPrimeWinnerColours
import Submission.FiniteSupportSchur

/-! Uniform harmonic prime-winner cancellation. This is an ℓ¹ statement about
harmonic currents, not natural-density convergence. -/
namespace Erdos371
open Finset Filter FiniteInformation DilationSpectrum
open scoped Topology
set_option autoImplicit false

noncomputable def primeWinnerHarmonicCurrent (N p : ℕ) : ℝ :=
  harmonicMean (N+1) (fun n => if primeWinner n=p then factorSign n else 0)

lemma primeWinner_harmonic_current_test (N B : ℕ) (hB : N+2<B) (s : ℕ → ℝ) :
    (∑ p ∈ range B, s p*primeWinnerHarmonicCurrent N p) =
      harmonicMean (N+1) (fun n => s (primeWinner n)*factorSign n) := by
  classical
  unfold primeWinnerHarmonicCurrent harmonicMean
  simp only [← mul_div_assoc,Finset.mul_sum,← sum_div]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn' := (mem_Icc.mp hn).2
  have hb : primeWinner n<B := by
    have hh : primeWinner n≤n+1 :=
      max_le (Nat.maxPrimeFac_le.trans (by omega)) Nat.maxPrimeFac_le
    omega
  rw [sum_eq_single (primeWinner n)]
  · simp
  · intro p hp hne
    rw [if_neg (Ne.symm hne)]
    simp
  · intro hp
    exact False.elim (hp (mem_range.mpr hb))

lemma primeWinner_sign_test_harmonic_zero (s : ℕ → ℝ) (hs : ∀ p, s p=1 ∨ s p = -1) :
    Tendsto (fun N => harmonicMean (N+1) (fun n => s (primeWinner n)*factorSign n))
      atTop (𝓝 0) := by
  classical
  let g (p : ℕ) : Bool := decide (s p=1)
  let w (b : Bool) : ℝ := if b then 1 else -1
  have he (p : ℕ) : w (g p)=s p := by
    rcases hs p with h|h <;> norm_num [w,g,h]
  have hw (b : Bool) : |w b| ≤ 1 := by cases b <;> norm_num [w]
  simpa only [he,mul_comm] using primeWinner_coloured_harmonic_zero g w hw

/-- Total variation of the harmonic imbalance over all prime winners tends
to zero after division by the harmonic normalization. -/
theorem primeWinner_harmonic_l1_zero :
    Tendsto (fun N => ∑ p ∈ range (N+3), |primeWinnerHarmonicCurrent N p|)
      atTop (𝓝 0) := by
  let f (N p : ℕ) := primeWinnerHarmonicCurrent (N-3) p
  have hweak (s : ℕ → ℝ) (hs : ∀ p, s p=1 ∨ s p = -1) :
      Tendsto (fun N => ∑ p ∈ range N, s p*f N p) atTop (𝓝 0) := by
    have hsub : Tendsto (fun N : ℕ => N-3) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop (b+3)] with N hN
      omega
    have ht := (primeWinner_sign_test_harmonic_zero s hs).comp hsub
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
    exact (primeWinner_harmonic_current_test (N-3) N (by omega) s).symm
  have ht := (triangular_schur_of_sign_tests f hweak).comp (tendsto_add_atTop_nat 3)
  simpa only [f,Function.comp_def,Nat.add_sub_cancel] using ht

/-- Uniformity over endpoint-dependent weights of magnitude at most one.
The weights themselves need not have any stability property. -/
theorem primeWinner_bounded_weights_harmonic_zero (w : ℕ → ℕ → ℝ)
    (hw : ∀ N p, |w N p| ≤ 1) :
    Tendsto (fun N => harmonicMean (N+1) (fun n => w N (primeWinner n)*factorSign n))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm _ primeWinner_harmonic_l1_zero
  intro N
  rw [← primeWinner_harmonic_current_test N (N+3) (by omega) (w N),Real.norm_eq_abs]
  calc
    _ ≤ ∑ p ∈ range (N+3), |w N p*primeWinnerHarmonicCurrent N p| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hw N p)

#print axioms primeWinner_harmonic_l1_zero
#print axioms primeWinner_bounded_weights_harmonic_zero
end Erdos371
