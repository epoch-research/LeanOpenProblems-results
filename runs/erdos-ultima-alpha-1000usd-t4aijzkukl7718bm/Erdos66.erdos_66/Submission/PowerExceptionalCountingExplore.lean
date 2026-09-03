import Submission.PowerExceptionalProfileExplore
import Submission.SummableScaleCountingExplore
import Submission.PotentialPointwiseEnvelopeExplore
import Submission.DensityOneLogLimitExplore

/-! Polynomially sparse fixed-tolerance exceptions, together with the
previous uniform envelopes and one harmonically summable exceptional set. -/
namespace Erdos66PowerExceptionalCounting
open Filter AdditiveCombinatorics Erdos66Counting Erdos66PowerExceptionalProfile
  Erdos66SummableScaleCounting Erdos66PotentialPointwiseEnvelope
  Erdos66SummableExceptionalSet Erdos66DensityOneLogLimit
open scoped Classical Topology
set_option maxHeartbeats 1500000

lemma harmonic_of_power_weight (E : Set ℕ) (α : ℝ) (hα : 0≤α)
    (hs : Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2)^(1-α : ℝ) else 0)) :
    Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0) := by
  apply Summable.of_nonneg_of_le (fun n ↦ by split_ifs <;> positivity) _ hs
  intro n
  by_cases hn : n∈E
  · simp only [if_pos hn,weight_identity]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) n]) hα
    simpa only [Real.rpow_zero] using hh
  · simp only [if_neg hn,le_refl]

/-- A fixed-c set with polynomially negligible bad counts at every fixed
tolerance, and all the previously obtained constant-width envelopes. -/
theorem exists_power_exceptions_and_envelopes (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ,
      (∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧
        Summable (fun n : ℕ ↦ if ε≤|(sumRep A n : ℝ)/Real.log n-c|
          then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) ∧
        Tendsto (fun N ↦ (count {n | ε≤|(sumRep A n : ℝ)/Real.log n-c|} N : ℝ) /
          ((N:ℝ)+2)^(1-α : ℝ)) atTop (𝓝 0)) ∧
      (∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
        |(sumRep A n : ℝ)/Real.log n-c| ≤ c/((j:ℝ)+1)+32*((j:ℝ)+1)) := by
  obtain ⟨A,hA⟩ := exists_power_potentials c hc
  refine ⟨A,?_,?_⟩
  · intro ε hε
    obtain ⟨α,hα,hα1,hs⟩ := power_exceptions_of_potentials A c hc hA ε hε
    exact ⟨α,hα,hα1,hs,count_div_power_zero _ (1-α) (by linarith) hs⟩
  · intro j
    have hs := harmonic_potential_of_power A c (1/((j:ℝ)+1)) hc (by positivity) (hA j)
    have hs' : Summable (fun n : ℕ ↦ if 0≤n then
        Erdos66BiasedTailPotential.potential (1/((j:ℝ)+1)) (c*Real.log n) (sumRep A n)/((n:ℝ)+2)
        else 0) := by simpa only [Nat.zero_le,if_true] using hs
    have hh := eventual_error_envelope A c (1/((j:ℝ)+1)) 0 (by positivity) hs'
    have he : (1/((j:ℝ)+1))*c+32/(1/((j:ℝ)+1)) = c/((j:ℝ)+1)+32*((j:ℝ)+1) := by
      field_simp
    rwa [he] at hh

/-- Joint endpoint: c and A stay fixed through all tolerances. Each fixed
bad set has its own positive power saving; the single diagonal exception
set is only asserted to be harmonically summable. -/
theorem exists_power_saving_density_one_profile (c : ℝ) (hc : 0<c) :
    ∃ A E : Set ℕ,
      Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0) ∧
      Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then c else (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) ∧
      (∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧
        Summable (fun n : ℕ ↦ if ε≤|(sumRep A n : ℝ)/Real.log n-c|
          then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) ∧
        Tendsto (fun N ↦ (count {n | ε≤|(sumRep A n : ℝ)/Real.log n-c|} N : ℝ) /
          ((N:ℝ)+2)^(1-α : ℝ)) atTop (𝓝 0)) ∧
      (∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
        |(sumRep A n : ℝ)/Real.log n-c| ≤ c/((j:ℝ)+1)+32*((j:ℝ)+1)) := by
  obtain ⟨A,hA,henv⟩ := exists_power_exceptions_and_envelopes c hc
  have hh : ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if ε≤|(sumRep A n : ℝ)/Real.log n-c| then 1/((n:ℝ)+2) else 0) := by
    intro ε hε
    obtain ⟨α,hα,hα1,hs,hlim⟩ := hA ε hε
    exact harmonic_of_power_weight _ α hα.le hs
  obtain ⟨E,hE,hlim⟩ := exists_exceptional_set
    (fun n ↦ (sumRep A n : ℝ)/Real.log n) c (fun n ↦ 1/((n:ℝ)+2))
    (fun n ↦ by positivity) hh
  exact ⟨A,E,hE,density_zero_of_harmonic_summable E hE,hlim,hA,henv⟩

end Erdos66PowerExceptionalCounting
