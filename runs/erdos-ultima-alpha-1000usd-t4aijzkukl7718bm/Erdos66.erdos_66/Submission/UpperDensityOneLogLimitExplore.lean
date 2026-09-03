import Submission.PotentialPointwiseEnvelopeExplore
import Submission.DensityOneLogLimitExplore

/-! Fixed-coefficient density-one convergence together with uniform
logarithmic representation envelopes. The exceptional targets remain. -/
namespace Erdos66UpperDensityOneLogLimit
open Filter AdditiveCombinatorics Erdos66PotentialPointwiseEnvelope
  Erdos66DensityOneLogLimit Erdos66SummableExceptionalSet Erdos66Counting
open scoped Classical Topology

lemma global_envelope_of_eventual (A : Set ℕ) (C : ℝ) (hC : 0≤C)
    (h : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ) ≤ C*Real.log n) :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, (sumRep A n : ℝ) ≤ K+C*Real.log ((n:ℝ)+2) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨(N+2:ℕ),by positivity,fun n ↦ ?_⟩
  have hlo : 0≤C*Real.log ((n:ℝ)+2) := mul_nonneg hC
    (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  by_cases hn : max N 1≤n
  · have hnN : N≤n := (le_max_left _ _).trans hn
    have hn1 : 1≤n := (le_max_right _ _).trans hn
    have hs := Real.log_le_log (by exact_mod_cast (show 0<n by omega) : (0:ℝ)<n)
      (show (n:ℝ)≤(n:ℝ)+2 by linarith)
    have hh := (hN n hnN).trans (mul_le_mul_of_nonneg_left hs hC)
    exact hh.trans (le_add_of_nonneg_left (by positivity))
  · have hh : (sumRep A n : ℝ) ≤ N+2 := by
      exact_mod_cast (show sumRep A n ≤ N+2 from (sumRep_le_succ A n).trans (by omega))
    push_cast
    linarith

/-- A density-one fixed-c construction with a global logarithmic upper
bound, including its exceptional targets. -/
theorem exists_globally_bounded_log_limit_off_exception (c : ℝ) (hc : 0<c) :
    ∃ (A E : Set ℕ) (K : ℝ), 0≤K ∧
      (∀ n : ℕ, (sumRep A n : ℝ) ≤ K+(2*c+32)*Real.log ((n:ℝ)+2)) ∧
      Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0) ∧
      Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then c else (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  obtain ⟨A,hA,hu⟩ := exists_exceptions_and_upper_envelope c hc
  obtain ⟨K,hK,hupper⟩ := global_envelope_of_eventual A (2*c+32) (by positivity) hu
  obtain ⟨E,hE,hlim⟩ := exists_exceptional_set
    (fun n ↦ (sumRep A n : ℝ)/Real.log n) c (fun n ↦ 1/((n:ℝ)+2))
    (fun n ↦ by positivity) hA
  exact ⟨A,E,K,hK,hupper,hE,density_zero_of_harmonic_summable E hE,hlim⟩

/-- For c>128 the same construction can be an eventual additive basis,
with a positive logarithmic lower envelope at every target. -/
theorem exists_two_sided_log_limit_off_exception (c : ℝ) (hc : 128<c) :
    ∃ A E : Set ℕ,
      (∀ᶠ n : ℕ in atTop,
        (c/2-64)*Real.log n ≤ (sumRep A n : ℝ) ∧
        (sumRep A n : ℝ) ≤ (3*c/2+64)*Real.log n) ∧
      Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0) ∧
      Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then c else (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  obtain ⟨A,hA,hbound⟩ := exists_exceptions_and_all_envelopes c (by linarith)
  obtain ⟨E,hE,hlim⟩ := exists_exceptional_set
    (fun n ↦ (sumRep A n : ℝ)/Real.log n) c (fun n ↦ 1/((n:ℝ)+2))
    (fun n ↦ by positivity) hA
  refine ⟨A,E,?_,hE,density_zero_of_harmonic_summable E hE,hlim⟩
  have hh := hbound 1
  norm_num only [Nat.cast_one,one_add_one_eq_two,show (32:ℝ)*2=64 by norm_num] at hh
  filter_upwards [hh,eventually_ge_atTop 2] with n hn hn2
  have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  obtain ⟨hlo,hhi⟩ := abs_le.mp hn
  constructor
  · apply (le_div_iff₀ hln).mp
    linarith
  · apply (div_le_iff₀ hln).mp
    linarith

end Erdos66UpperDensityOneLogLimit
