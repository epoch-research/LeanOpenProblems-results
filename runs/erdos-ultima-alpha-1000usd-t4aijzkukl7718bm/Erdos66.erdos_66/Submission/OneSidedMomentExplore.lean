import Submission.AbelErrorEnergyExplore
import Submission.CumulativeRoundingErrorExplore
import Submission.WeightedLogExplore

/-! A one-sided moment restriction on candidate rounding rules.
This does not settle the existential logarithmic representation conjecture. -/
namespace Erdos66OneSidedMoment
open Filter AdditiveCombinatorics Erdos66Generating Erdos66Fractional
  Erdos66Rounding Erdos66CumulativeRoundingError Erdos66AbelErrorEnergy
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma finite_second_moment (e : ℕ → ℝ) (K D δ : ℝ) (hK : 0 ≤ K)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hu : ∀ n, e n ≤ K)
    (he : ∀ n, |e n| ≤ δ * (harmonic n : ℝ) + D) (n : ℕ) :
    prefixSum (fun i ↦ (e i)^2) n ≤
      K * (D + δ * (harmonic n : ℝ)) * ((n:ℝ)+1) +
      (K + D + δ * (harmonic n : ℝ)) * |prefixSum e n| := by
  let B := D + δ * (harmonic n : ℝ)
  have hB : 0 ≤ B := add_nonneg hD (mul_nonneg hδ (harmonic_nonneg n))
  have hp (i : ℕ) (hi : i ∈ Finset.range (n+1)) :
      (e i)^2 ≤ (K-B)*e i + K*B := by
    have him : (harmonic i : ℝ) ≤ harmonic n :=
      harmonic_monotone_real (by have := Finset.mem_range.mp hi; omega)
    have hl : -B ≤ e i := by
      have := (abs_le.mp (he i)).1
      have := mul_le_mul_of_nonneg_left him hδ
      dsimp [B]; linarith
    have hprod := mul_nonneg (sub_nonneg.mpr (hu i)) (by linarith : 0 ≤ e i+B)
    nlinarith
  have hs := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hs
  change prefixSum (fun i ↦ (e i)^2) n ≤ (K-B)*prefixSum e n + K*(((n:ℝ)+1)*B) at hs
  have hb : (K-B)*prefixSum e n ≤ (K+B)*|prefixSum e n| := by
    calc
      _ ≤ |(K-B)*prefixSum e n| := le_abs_self _
      _ = |K-B| * |prefixSum e n| := abs_mul _ _
      _ ≤ (K+B)*|prefixSum e n| := by
        gcongr
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hK, abs_of_nonneg hB])
  dsimp [B] at hs hb
  linarith

/-- Small signed prefix means and a fixed upper error bound rule out
logarithmic-scale second-moment mass if the error itself is sublogarithmic. -/
lemma second_moment_limit_of_one_sided_bound (e : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ n, e n ≤ K)
    (he : Tendsto (fun n ↦ e n / Real.log n) atTop (𝓝 0))
    (hm : Tendsto (fun n ↦ prefixSum e n / ((n:ℝ)+1)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ prefixSum (fun i ↦ (e i)^2) n /
      (((n:ℝ)+1)*Real.log n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (2*(K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : K*δ < ε := by
    have hx : δ*(2*(K+1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨D,hD,hbound⟩ := global_harmonic_error he hδ
  simp only [zero_mul,sub_zero] at hbound
  have hinv := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop (1:ℝ)
  have hfirst := ((hinv.const_mul D).add (harmonic_log_ratio.const_mul δ)).const_mul K
  have hsecond := (((hinv.const_mul (K+D)).add
    (harmonic_log_ratio.const_mul δ)).mul hm.abs)
  have hlim := hfirst.add hsecond
  simp only [mul_zero,add_zero,mul_one,zero_add,abs_zero] at hlim
  have hsmall := hlim.eventually_lt_const hδε
  filter_upwards [hsmall,eventually_ge_atTop 2] with n hn hn2
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hnpos : 0 < (n:ℝ)+1 := by positivity
  have hmoment := finite_second_moment e K D δ hK hD hδ.le hu hbound n
  have hnorm := div_le_div_of_nonneg_right hmoment (mul_pos hnpos hlog).le
  have heq :
      (K*(D+δ*(harmonic n:ℝ))*((n:ℝ)+1) +
        (K+D+δ*(harmonic n:ℝ))*|prefixSum e n|) /
        (((n:ℝ)+1)*Real.log n) =
      K*(D*(1/Real.log n)+δ*((harmonic n:ℝ)/Real.log n)) +
      ((K+D)*(1/Real.log n)+δ*((harmonic n:ℝ)/Real.log n)) *
        |prefixSum e n/((n:ℝ)+1)| := by
    rw [abs_div,abs_of_pos hnpos]
    field_simp
  rw [heq] at hnorm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i hi ↦ sq_nonneg _)
    · positivity)]
  exact hnorm.trans_lt hn

end Erdos66OneSidedMoment
