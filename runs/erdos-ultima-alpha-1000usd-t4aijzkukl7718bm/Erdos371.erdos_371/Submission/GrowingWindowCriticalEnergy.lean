import Submission.PrimeHarmonicWindowIncidence
import Submission.GrowingWindowPrimeWinnerNorm

/-! Critical prime-weighted energy of the NORMALIZED harmonic current vector
vanishes on every interval of diverging harmonic mass. Fixed-ratio windows
are not covered. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma reciprocalInterval_eq_shiftedMass (A M : ℕ) :
    reciprocalInterval (A+1) (A+M+2)=shiftedHarmonicMass A M := by
  rw [reciprocalInterval,sum_Ico_eq_sum_range,
    show A+M+2-(A+1)=M+1 by omega]
  unfold shiftedHarmonicMass shiftedHarmonicRaw
  apply sum_congr rfl
  intro n _
  push_cast
  congr 1
  ring

/-- A uniform bound at the critical prime weight, with a boundary error
which depends only on the harmonic mass, not on either endpoint or prime. -/
lemma shiftedPrimeWinnerCurrent_mul_label_bound (A M p : ℕ) :
    (p : ℝ)*|shiftedPrimeWinnerCurrent A M p|≤3+3/shiftedHarmonicMass A M := by
  have hH : 0<shiftedHarmonicMass A M := shiftedHarmonicMass_pos A M
  by_cases hp : p=0
  · subst p
    simp only [Nat.cast_zero,zero_mul]
    positivity
  have hb := primeWinner_harmonic_window_label_bound p (A+1) (A+M+2)
    (Nat.pos_of_ne_zero hp) (by omega) (by omega)
  rw [reciprocalInterval_eq_shiftedMass] at hb
  rw [shiftedPrimeWinnerCurrent_eq_raw_window,abs_div,abs_of_pos hH]
  calc
    _ = ((p : ℝ)*|rawPrimeWinnerHarmonic p (A+M+2)-rawPrimeWinnerHarmonic p (A+1)|)/
        shiftedHarmonicMass A M := by ring
    _ ≤ (3*(shiftedHarmonicMass A M+1))/shiftedHarmonicMass A M :=
      div_le_div_of_nonneg_right hb hH.le
    _ = _ := by field_simp

noncomputable def shiftedPrimeWinnerCriticalEnergy (A M : ℕ) : ℝ :=
  ∑ p ∈ range (A+M+3), (p : ℝ)*(shiftedPrimeWinnerCurrent A M p)^2

lemma shiftedPrimeWinnerCriticalEnergy_nonneg (A M : ℕ) :
    0≤shiftedPrimeWinnerCriticalEnergy A M := by
  unfold shiftedPrimeWinnerCriticalEnergy
  positivity

lemma shiftedPrimeWinnerCriticalEnergy_le_l1 (A M : ℕ) :
    shiftedPrimeWinnerCriticalEnergy A M ≤
      (3+3/shiftedHarmonicMass A M)*
        ∑ p ∈ range (A+M+3), |shiftedPrimeWinnerCurrent A M p| := by
  rw [shiftedPrimeWinnerCriticalEnergy,mul_sum]
  apply sum_le_sum
  intro p _
  have h := mul_le_mul_of_nonneg_right (shiftedPrimeWinnerCurrent_mul_label_bound A M p)
    (abs_nonneg (shiftedPrimeWinnerCurrent A M p))
  simpa only [mul_assoc,← pow_two,sq_abs] using h

/-- No logarithmic slack is needed here, but the currents are divided by
the harmonic mass and that mass MUST tend to infinity. -/
theorem primeWinner_growing_harmonic_critical_energy_zero (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedPrimeWinnerCriticalEnergy (A j) (M j)) atTop (𝓝 0) := by
  have hratio : Tendsto (fun j => (3 : ℝ)/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hH
  have ht := (hratio.const_add 3).mul (primeWinner_growing_harmonic_l1_zero A M hH)
  simp only [mul_zero] at ht
  exact squeeze_zero (fun j => shiftedPrimeWinnerCriticalEnergy_nonneg _ _)
    (fun j => shiftedPrimeWinnerCriticalEnergy_le_l1 _ _) ht

lemma shiftedPrimeWinnerCriticalEnergy_eq_tsum (A M : ℕ) :
    shiftedPrimeWinnerCriticalEnergy A M =
      ∑' p : ℕ, (p : ℝ)*(shiftedPrimeWinnerCurrent A M p)^2 := by
  classical
  symm
  apply tsum_eq_sum
  intro p hp
  rw [shiftedPrimeWinnerCurrent_zero_above A M p
    (by simp only [mem_range,not_lt] at hp; omega),zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero]

/-- A single harmonic-mass threshold works uniformly over both endpoints. -/
theorem primeWinner_uniform_long_harmonic_critical_energy (ε : ℝ) (hε : 0<ε) :
    ∃ R : ℝ, 0<R ∧ ∀ A M : ℕ, R≤shiftedHarmonicMass A M →
      shiftedPrimeWinnerCriticalEnergy A M<ε := by
  obtain ⟨R,hR,hl1⟩ := primeWinner_uniform_long_harmonic_l1 (ε/6) (by positivity)
  refine ⟨max R 1,lt_of_lt_of_le hR (le_max_left _ _),?_⟩
  intro A M hmass
  have hH : 1≤shiftedHarmonicMass A M := (le_max_right R 1).trans hmass
  have hc : 3+3/shiftedHarmonicMass A M≤6 := by
    have h := (div_le_iff₀ (shiftedHarmonicMass_pos A M)).mpr
      (show (3 : ℝ)≤3*shiftedHarmonicMass A M by linarith)
    linarith
  have hb := (shiftedPrimeWinnerCriticalEnergy_le_l1 A M).trans
    (mul_le_mul_of_nonneg_right hc (sum_nonneg (fun _ _ => abs_nonneg _)))
  have hs := hl1 A M ((le_max_left R 1).trans hmass)
  linarith

#print axioms shiftedPrimeWinnerCurrent_mul_label_bound
#print axioms primeWinner_growing_harmonic_critical_energy_zero
#print axioms primeWinner_uniform_long_harmonic_critical_energy
end Erdos371
