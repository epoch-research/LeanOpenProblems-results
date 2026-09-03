import Submission.DifferenceNaturalPatternExplore
import Submission.ExactBracketHostEnvelopeExplore

/-! One exact-bracket host carrying local differences, boundary counts,
central triple caps, and all two-sided power-cost rows simultaneously. -/
namespace Erdos66JointDifferencePatternHost
open Filter AdditiveCombinatorics Erdos66DifferenceNaturalPattern
  Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern
  Erdos66JointBoundaryTriplePatterns Erdos66GeneralCentralTripleMean
  Erdos66TripleIntersectionGeometry Erdos66TripleIntersectionMean
  Erdos66BernoulliMatchingPolynomial Erdos66Fractional Erdos66Generating
  Erdos66BoundaryPairPotential Erdos66BoundaryPairCounts Erdos66CentralTripleCounts
  Erdos66JointBoundaryTripleCounts Erdos66LocalDifferencePotential
  Erdos66ClampedPrefixContinuation Erdos66PowerExceptionalProfile
  Erdos66ExactBracketHostEnvelope
open scoped Classical Topology
set_option maxHeartbeats 2400000

noncomputable def extendedTests (T : ℕ → ℕ) (m : ℕ) : Pattern :=
  let q := Nat.unpair m
  if q.1=2 then
    let r := Nat.unpair q.2
    let s := Nat.unpair r.2
    if 0<s.1 ∧ s.1<r.1 ∧ s.2<2 then differencePattern r.1 s.1 s.2 else zeroPattern
  else tests T m

lemma extendedTests_boundary (T : ℕ → ℕ) (j n : ℕ) (hn : (cutoff j)^2 ≤ n) :
    extendedTests T (boundaryCode j n)=boundaryPattern j n := by
  rw [extendedTests]
  simp only [boundaryCode,Nat.unpair_pair,show ¬(0 : ℕ)=2 by omega,if_false]
  exact tests_boundary T j n hn

lemma extendedTests_triple (T : ℕ → ℕ) (C h N n z : ℕ) (hN : T C ≤ N) (hn : n ≤ C*N) :
    extendedTests T (tripleCode C h N n z)=triplePattern N n z := by
  rw [extendedTests]
  simp only [tripleCode,Nat.unpair_pair,show ¬(1 : ℕ)=2 by omega,if_false]
  exact tests_triple T C h N n z hN hn

lemma extendedTests_difference (T : ℕ → ℕ) (N d b : ℕ) (hd : 0<d) (hdN : d<N) (hb : b<2) :
    extendedTests T (differenceCode N d b)=differencePattern N d b := by
  simp only [extendedTests,differenceCode,Nat.unpair_pair,if_true,hd,hdN,hb,and_self]

lemma extendedTests_mean (T : ℕ → ℕ)
    (hT : ∀ C N, T C ≤ N → ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ profile i.val) ≤ Real.exp 1)
    (m : ℕ) : (extendedTests T m).eval profile ≤ 3*((m : ℝ)+2) := by
  dsimp only [extendedTests]
  split_ifs with htag hactive
  · apply (differencePattern_mean _ _ _ hactive.1).trans
    have hn := (Nat.unpair_left_le (Nat.unpair m).2).trans (Nat.unpair_right_le m)
    have hn' : (((Nat.unpair (Nat.unpair m).2).1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hn
    linarith
  · simp only [zeroPattern_eval]
    positivity
  · exact tests_mean T hT m

/-- The old boundary and triple constants are unchanged. The added local
difference estimate is 144 log(N+1), with both endpoints in [N,2N). -/
theorem exists_joint_difference_host :
    ∃ (A : Set ℕ) (K : ℝ) (ND : ℕ) (NB : ℕ → ℕ) (NT : ℕ → ℕ → ℕ),
      0 ≤ K ∧ (∀ L, PrefixBrackets profile A L) ∧
      (∀ n, (sumRep A n : ℝ) ≤ K+34*Real.log ((n : ℝ)+2)) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j : ℝ)+1)) n (sumRep A n))) ∧
      (∀ N d, ND ≤ N → 0<d → (localDiff A N d : ℝ) ≤ 144*Real.log ((N : ℝ)+1)) ∧
      (∀ j n, NB j ≤ n → ((j : ℝ)+1)*((boundary A (cutoff j) n).card : ℝ) ≤
        20*Real.log ((n : ℝ)+1)) ∧
      (∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
        (fiber A N n z).card ≤ tripleCap h) := by
  have hcut (C : ℕ) : ∃ T : ℕ, ∀ N≥T, ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ profile i.val) ≤ Real.exp 1 :=
    eventually_atTop.mp (eventually_comparable_poly_mean C)
  choose T hT using hcut
  obtain ⟨A,M,hbr,hP,hcost⟩ := Erdos66ExactBracketPatternHost.exists_polynomial_pattern_bounds
    (extendedTests T) (extendedTests_mean T hT)
  obtain ⟨K,hK,henv⟩ := envelope_of_power_rows A hcost
  let ND := max 2 M
  let NB : ℕ → ℕ := fun j ↦ max ((cutoff j)^2) (max 1 (max j M))
  let NT : ℕ → ℕ → ℕ := fun C h ↦ max (T C) (max 1 (max C (max h M)))
  refine ⟨A,K,ND,NB,NT,hK,hbr,henv,hcost,?_,?_,?_⟩
  · intro N d hN hd
    have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
    have hNM : M ≤ N := (le_max_right _ _).trans hN
    apply localDiff_of_pattern_budget A M N d hN2 hNM hd
    intro b hb hdN
    have hh := hP (differenceCode N d b)
    rwa [extendedTests_difference T N d b hd hdN hb] at hh
  · intro j n hn
    have hn' : max ((cutoff j)^2) (max 1 (max j M)) ≤ n := hn
    have hh := hP (boundaryCode j n)
    rw [extendedTests_boundary T j n (by omega)] at hh
    exact boundary_count_of_budget A j n M (by omega) (by omega) (by omega) hh
  · intro C h N n z hN hn hz hnz
    have hN' : max (T C) (max 1 (max C (max h M))) ≤ N := hN
    have hh' := hP (tripleCode C h N n z)
    rw [extendedTests_triple T C h N n z (by omega) hn] at hh'
    exact triple_count_of_budget A C h N n z M (by omega) (by omega) (by omega) (by omega) hn hz hnz hh'

end Erdos66JointDifferencePatternHost
