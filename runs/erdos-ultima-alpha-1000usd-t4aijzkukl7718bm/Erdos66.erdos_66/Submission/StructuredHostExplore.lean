import Submission.HostPatternSelectionExplore
import Submission.JointBoundaryTripleCountsExplore
import Submission.DominatedScaledProfileExplore
import Submission.PotentialPointwiseEnvelopeExplore

/-! A high-coefficient host with a positive all-target lower envelope and
joint boundary/triple control. This is not an asymptotic witness. -/
namespace Erdos66StructuredHost
open Filter AdditiveCombinatorics Erdos66HostPatternSelection Erdos66HostPatternMean
  Erdos66JointBoundaryTripleCounts Erdos66JointBoundaryTriplePatterns Erdos66RarePatternCodeGrowth
  Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern Erdos66NaturalPatternRestriction
  Erdos66BoundaryPairCounts Erdos66BoundaryPairMean Erdos66DisjointMatchingPolynomial
  Erdos66BernoulliMatchingPolynomial Erdos66CentralTripleCounts Erdos66TripleIntersectionMean
  Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66DominatedScaledProfile
  Erdos66Generating Erdos66PowerExceptionalProfile Erdos66PotentialPointwiseEnvelope
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma hostBoundaryPattern_value (A : Set ℕ) (j n : ℕ) :
    (hostBoundaryPattern j n).value (fun i ↦ decide (i∈A))=
      Real.exp (((j:ℝ)+1)*((boundary A (hostCutoff j) n).card:ℝ)) := by
  rw [hostBoundaryPattern,Pattern.value,matchingPattern_eval]
  change matchingPoly (boundaryPairs n (hostCutoff j) n) pairCoords ((j:ℝ)+1)
    (fun i ↦ bit (restrict A n i))=_
  rw [matchingPoly_binary_disjoint _ _ (boundaryPairs_disjoint n (hostCutoff j) n),
    selected_boundary_card n (hostCutoff j) n (hostCutoff_ge_two j),boundary_restrict A n (hostCutoff j) n le_rfl]

lemma host_boundary_count_of_budget (A : Set ℕ) (j n M : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) (hM : M ≤ n)
    (hbudget : (hostBoundaryPattern j n).value (fun i ↦ decide (i∈A)) ≤ ((boundaryCode j n:ℝ)+M+2)^4) :
    ((j:ℝ)+1)*((boundary A (hostCutoff j) n).card:ℝ) ≤ 20*Real.log ((n:ℝ)+1) := by
  rw [hostBoundaryPattern_value] at hbudget
  have hcode : (boundaryCode j n:ℝ)+M+2 ≤ ((n:ℝ)+1)^5 :=
    by exact_mod_cast boundaryCode_shift_bound j n M hn hj hM
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (boundaryCode j n:ℝ)+M+2) hcode 4
  have hh := Real.log_le_log (Real.exp_pos _) (hbudget.trans hpow)
  rw [Real.log_exp,Real.log_pow,Real.log_pow] at hh
  norm_num at hh
  linarith only [hh]

lemma host_envelope_of_power (A : Set ℕ)
    (hcost : ∀ j : ℕ, Summable (fun n ↦ powerCost 1024 (1/((j:ℝ)+1)) n (sumRep A n))) :
    ∀ᶠ n : ℕ in atTop, 448*Real.log (n:ℝ) ≤ (sumRep A n:ℝ) ∧
      (sumRep A n:ℝ) ≤ 1600*Real.log (n:ℝ) := by
  have hs := harmonic_potential_of_power A 1024 (1/2) (by norm_num) (by norm_num)
    (by simpa only [Nat.cast_one,one_add_one_eq_two] using hcost 1)
  have he := eventual_error_envelope A 1024 (1/2) 0 (by norm_num) (by simpa using hs)
  filter_upwards [he,eventually_ge_atTop 2] with n hn hn2
  have hlog : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  norm_num only [one_div,inv_pos,div_pos] at hn
  obtain ⟨hl,hu⟩ := abs_le.mp hn
  constructor
  · apply (le_div_iff₀ hlog).mp
    linarith
  · apply (div_le_iff₀ hlog).mp
    linarith

 theorem exists_structured_host : ∃ (A : Set ℕ) (p : ℕ → ℝ) (NB : ℕ → ℕ) (NT : ℕ → ℕ → ℕ),
    (∀ n, 0 ≤ p n ∧ p n ≤ 1) ∧
    Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 (1024:ℝ)) ∧
    (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1024 (1/((j:ℝ)+1)) n (sumRep A n))) ∧
    (∀ j n, NB j ≤ n → ((j:ℝ)+1)*((boundary A (hostCutoff j) n).card:ℝ) ≤ 20*Real.log ((n:ℝ)+1)) ∧
    (∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
      (fiber A N n z).card ≤ tripleCap h) ∧
    (∀ᶠ n : ℕ in atTop, 448*Real.log (n:ℝ) ≤ (sumRep A n:ℝ) ∧
      (sumRep A n:ℝ) ≤ 1600*Real.log (n:ℝ)) := by
  obtain ⟨p,hp,hdom,hconv⟩ := exists_dominated_scaled_profile 1024 (by norm_num)
  norm_num only [show Real.sqrt (1024:ℝ)=32 by norm_num] at hdom
  obtain ⟨A,M,T,hbr,hcost,hB,hT⟩ := exists_host_pattern_bounds p hp hdom hconv
  let NB : ℕ → ℕ := fun j ↦ max ((hostCutoff j)^2) (max 1 (max j M))
  let NT : ℕ → ℕ → ℕ := fun C h ↦ max (T C) (max 1 (max C (max h M)))
  refine ⟨A,p,NB,NT,hp,hconv,hbr,hcost,?_,?_,host_envelope_of_power A hcost⟩
  · intro j n hn
    have hn' : max ((hostCutoff j)^2) (max 1 (max j M)) ≤ n := hn
    exact host_boundary_count_of_budget A j n M (by omega) (by omega) (by omega) (hB j n (by omega))
  · intro C h N n z hN hn hz hnz
    have hN' : max (T C) (max 1 (max C (max h M))) ≤ N := hN
    exact triple_count_of_budget A C h N n z M (by omega) (by omega) (by omega) (by omega) hn hz hnz
      (hT C h N n z (by omega) hn)

end Erdos66StructuredHost
