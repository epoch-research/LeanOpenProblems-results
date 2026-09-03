import Submission.PrefixBalancedPowerProfileExplore
import Submission.PowerExceptionalCountingExplore

/-! Joint fixed-coefficient construction with prefix discrepancy, power-saving
exceptional counts, and convergence outside a harmonically summable set. -/
namespace Erdos66PrefixBalancedDensityOne
open Filter AdditiveCombinatorics Erdos66PrefixBalancedPowerProfile Erdos66PowerExceptionalProfile
  Erdos66PowerExceptionalCounting Erdos66SummableScaleCounting Erdos66PotentialPointwiseEnvelope
  Erdos66SummableExceptionalSet Erdos66DensityOneLogLimit Erdos66Counting Erdos66Generating
open scoped Classical Topology
set_option maxHeartbeats 1600000

 theorem exists_balanced_density_one_profile (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1)
    (c : ℝ) (hc : 0<c)
    (hconv : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c)) :
    ∃ A E : Set ℕ,
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)|≤1) ∧
      Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0) ∧
      Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then c else (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) ∧
      (∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧
        Summable (fun n : ℕ ↦ if ε≤|(sumRep A n : ℝ)/Real.log n-c|
          then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) ∧
        Tendsto (fun N ↦ (count {n | ε≤|(sumRep A n : ℝ)/Real.log n-c|} N : ℝ) /
          ((N:ℝ)+2)^(1-α : ℝ)) atTop (𝓝 0)) ∧
      (∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
        |(sumRep A n : ℝ)/Real.log n-c|≤c/((j:ℝ)+1)+32*((j:ℝ)+1)) := by
  obtain ⟨A,hbr,hA⟩ := exists_balanced_power_potentials p hp c hc hconv
  have hpower := power_exceptions_of_potentials A c hc hA
  have hh : ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if ε≤|(sumRep A n : ℝ)/Real.log n-c| then 1/((n:ℝ)+2) else 0) := by
    intro ε hε
    obtain ⟨α,hα,hα1,hs⟩ := hpower ε hε
    exact harmonic_of_power_weight _ α hα.le hs
  obtain ⟨E,hE,hlim⟩ := exists_exceptional_set
    (fun n ↦ (sumRep A n : ℝ)/Real.log n) c (fun n ↦ 1/((n:ℝ)+2))
    (fun n ↦ by positivity) hh
  refine ⟨A,E,hbr,hE,density_zero_of_harmonic_summable E hE,hlim,?_,?_⟩
  · intro ε hε
    obtain ⟨α,hα,hα1,hs⟩ := hpower ε hε
    exact ⟨α,hα,hα1,hs,count_div_power_zero _ (1-α) (by linarith) hs⟩
  · intro j
    have hs := harmonic_potential_of_power A c (1/((j:ℝ)+1)) hc (by positivity) (hA j)
    have hs' : Summable (fun n : ℕ ↦ if 0≤n then
        Erdos66BiasedTailPotential.potential (1/((j:ℝ)+1)) (c*Real.log n) (sumRep A n)/((n:ℝ)+2)
        else 0) := by simpa only [Nat.zero_le,if_true] using hs
    have hh := eventual_error_envelope A c (1/((j:ℝ)+1)) 0 (by positivity) hs'
    have he : (1/((j:ℝ)+1))*c+32/(1/((j:ℝ)+1))=c/((j:ℝ)+1)+32*((j:ℝ)+1) := by field_simp
    rwa [he] at hh

end Erdos66PrefixBalancedDensityOne
