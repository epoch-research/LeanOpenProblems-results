import Submission.ExactBracketPatternHostExplore
import Submission.UpperDensityOneLogLimitExplore

/-! The exact-bracket joint-pattern host also has a global logarithmic
representation envelope, extracted from its existing power-cost row. -/
namespace Erdos66ExactBracketHostEnvelope
open Filter AdditiveCombinatorics Erdos66ExactBracketPatternHost
  Erdos66PowerExceptionalProfile Erdos66PotentialPointwiseEnvelope
  Erdos66UpperDensityOneLogLimit Erdos66ClampedPrefixContinuation Erdos66Fractional
  Erdos66JointBoundaryTripleCounts Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential
  Erdos66CentralTripleCounts
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma envelope_of_power_rows (A : Set ℕ)
    (hcost : ∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j : ℝ)+1)) n (sumRep A n))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n, (sumRep A n : ℝ) ≤ K+34*Real.log ((n : ℝ)+2) := by
  have hc := hcost 0
  simp only [Nat.cast_zero,zero_add,div_one] at hc
  have hs := harmonic_potential_of_power A 1 1 (by norm_num) (by norm_num) hc
  have hs' : Summable (fun n : ℕ ↦ if 0 ≤ n then
      Erdos66BiasedTailPotential.potential 1 (1*Real.log n) (sumRep A n)/((n : ℝ)+2) else 0) := by
    simpa only [Nat.zero_le,if_true] using hs
  have he := eventual_error_envelope A 1 1 0 (by norm_num) hs'
  have hu : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ) ≤ 34*Real.log n := by
    filter_upwards [he,eventually_ge_atTop 2] with n hn hn2
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hh := (abs_le.mp hn).2
    apply (div_le_iff₀ hl).mp
    norm_num only [one_mul,div_one] at hh
    linarith
  exact global_envelope_of_eventual A 34 (by norm_num) hu

/-- All clauses concern the same set, including the exact original brackets. -/
theorem exists_exact_bracket_host : ∃ (A : Set ℕ) (K : ℝ) (NB : ℕ → ℕ) (NT : ℕ → ℕ → ℕ),
    0 ≤ K ∧
    (∀ L, PrefixBrackets profile A L) ∧
    (∀ n, (sumRep A n : ℝ) ≤ K+34*Real.log ((n : ℝ)+2)) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j : ℝ)+1)) n (sumRep A n))) ∧
    (∀ j n, NB j ≤ n → ((j : ℝ)+1)*((boundary A (cutoff j) n).card : ℝ) ≤
      20*Real.log ((n : ℝ)+1)) ∧
    (∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
      (fiber A N n z).card ≤ tripleCap h) := by
  obtain ⟨A,NB,NT,hbr,hcost,hB,hT⟩ := Erdos66ExactBracketPatternHost.exists_joint_boundary_triple_rounding
  obtain ⟨K,hK,henv⟩ := envelope_of_power_rows A hcost
  exact ⟨A,K,NB,NT,hK,hbr,henv,hcost,hB,hT⟩

end Erdos66ExactBracketHostEnvelope
