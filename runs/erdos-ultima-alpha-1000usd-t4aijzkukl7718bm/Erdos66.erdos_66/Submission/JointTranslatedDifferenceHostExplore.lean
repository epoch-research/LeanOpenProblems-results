import Submission.JointDifferencePatternHostExplore
import Submission.TranslatedDifferencePatternExplore

/-! A single exact-bracket host with both local and translated-window
nonzero-difference controls, in addition to all prior joint certificates. -/
namespace Erdos66JointTranslatedDifferenceHost
open Filter AdditiveCombinatorics Erdos66JointDifferencePatternHost
  Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern
  Erdos66JointBoundaryTriplePatterns Erdos66GeneralCentralTripleMean
  Erdos66TripleIntersectionGeometry Erdos66TripleIntersectionMean
  Erdos66BernoulliMatchingPolynomial Erdos66Fractional Erdos66Generating
  Erdos66BoundaryPairPotential Erdos66BoundaryPairCounts Erdos66CentralTripleCounts
  Erdos66JointBoundaryTripleCounts Erdos66LocalDifferencePotential
  Erdos66ClampedPrefixContinuation Erdos66PowerExceptionalProfile
  Erdos66ExactBracketHostEnvelope
open scoped Classical Topology
set_option maxHeartbeats 2600000

noncomputable def allTests (T : ℕ → ℕ) (m : ℕ) : Pattern :=
  let q := Nat.unpair m
  if q.1=3 then
    let r := Nat.unpair q.2
    let s := Nat.unpair r.2
    if 0<s.1 ∧ s.2<2 then Erdos66TranslatedDifferencePattern.differencePattern r.1 s.1 s.2 else zeroPattern
  else extendedTests T m

lemma allTests_boundary (T : ℕ → ℕ) (j n : ℕ) (hn : (cutoff j)^2 ≤ n) :
    allTests T (boundaryCode j n)=boundaryPattern j n := by
  rw [allTests]
  simp only [boundaryCode,Nat.unpair_pair,show ¬(0 : ℕ)=3 by omega,if_false]
  exact extendedTests_boundary T j n hn

lemma allTests_triple (T : ℕ → ℕ) (C h N n z : ℕ) (hN : T C ≤ N) (hn : n ≤ C*N) :
    allTests T (tripleCode C h N n z)=triplePattern N n z := by
  rw [allTests]
  simp only [tripleCode,Nat.unpair_pair,show ¬(1 : ℕ)=3 by omega,if_false]
  exact extendedTests_triple T C h N n z hN hn

lemma allTests_local_difference (T : ℕ → ℕ) (N d b : ℕ) (hd : 0<d) (hdN : d<N) (hb : b<2) :
    allTests T (Erdos66DifferenceNaturalPattern.differenceCode N d b)=
      Erdos66DifferenceNaturalPattern.differencePattern N d b := by
  rw [allTests]
  simp only [Erdos66DifferenceNaturalPattern.differenceCode,Nat.unpair_pair,show ¬(2 : ℕ)=3 by omega,if_false]
  exact extendedTests_difference T N d b hd hdN hb

lemma allTests_translated_difference (T : ℕ → ℕ) (N d b : ℕ) (hd : 0<d) (hb : b<2) :
    allTests T (Erdos66TranslatedDifferencePattern.differenceCode N d b)=
      Erdos66TranslatedDifferencePattern.differencePattern N d b := by
  simp only [allTests,Erdos66TranslatedDifferencePattern.differenceCode,Nat.unpair_pair,if_true,hd,hb,and_self]

lemma allTests_mean (T : ℕ → ℕ)
    (hT : ∀ C N, T C ≤ N → ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ profile i.val) ≤ Real.exp 1)
    (m : ℕ) : (allTests T m).eval profile ≤ 3*((m : ℝ)+2) := by
  dsimp only [allTests]
  split_ifs with htag hactive
  · apply (Erdos66TranslatedDifferencePattern.differencePattern_mean _ _ _ hactive.1).trans
    have hn := (Nat.unpair_left_le (Nat.unpair m).2).trans (Nat.unpair_right_le m)
    have hn' : (((Nat.unpair (Nat.unpair m).2).1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hn
    linarith
  · simp only [zeroPattern_eval]
    positivity
  · exact extendedTests_mean T hT m

/-- All clauses concern ONE set. In a translated-window pair, only the
smaller endpoint must lie in [N,2N); the second can be polynomially far away. -/
theorem exists_joint_translated_difference_host :
    ∃ (A : Set ℕ) (K : ℝ) (ND : ℕ) (NB : ℕ → ℕ) (NT : ℕ → ℕ → ℕ),
      0 ≤ K ∧ (∀ L, PrefixBrackets profile A L) ∧
      (∀ n, (sumRep A n : ℝ) ≤ K+34*Real.log ((n : ℝ)+2)) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j : ℝ)+1)) n (sumRep A n))) ∧
      (∀ N d, ND ≤ N → 0<d → (localDiff A N d : ℝ) ≤ 144*Real.log ((N : ℝ)+1)) ∧
      (∀ h N d, ND ≤ N → 0<d → d ≤ N^h →
        (Erdos66TranslatedDifferencePattern.translatedDiff A N d : ℝ) ≤
          16*((8*(h+1)+1 : ℕ) : ℝ)*Real.log ((N : ℝ)+1)) ∧
      (∀ j n, NB j ≤ n → ((j : ℝ)+1)*((boundary A (cutoff j) n).card : ℝ) ≤
        20*Real.log ((n : ℝ)+1)) ∧
      (∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
        (fiber A N n z).card ≤ tripleCap h) := by
  have hcut (C : ℕ) : ∃ T : ℕ, ∀ N≥T, ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ profile i.val) ≤ Real.exp 1 :=
    eventually_atTop.mp (eventually_comparable_poly_mean C)
  choose T hT using hcut
  obtain ⟨A,M,hbr,hP,hcost⟩ := Erdos66ExactBracketPatternHost.exists_polynomial_pattern_bounds
    (allTests T) (allTests_mean T hT)
  obtain ⟨K,hK,henv⟩ := envelope_of_power_rows A hcost
  let ND := max 3 M
  let NB : ℕ → ℕ := fun j ↦ max ((cutoff j)^2) (max 1 (max j M))
  let NT : ℕ → ℕ → ℕ := fun C h ↦ max (T C) (max 1 (max C (max h M)))
  refine ⟨A,K,ND,NB,NT,hK,hbr,henv,hcost,?_,?_,?_,?_⟩
  · intro N d hN hd
    have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
    have hNM : M ≤ N := (le_max_right _ _).trans hN
    apply Erdos66DifferenceNaturalPattern.localDiff_of_pattern_budget A M N d (by omega) hNM hd
    intro b hb hdN
    have hh := hP (Erdos66DifferenceNaturalPattern.differenceCode N d b)
    rwa [allTests_local_difference T N d b hd hdN hb] at hh
  · intro h N d hN hd hdN
    have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
    have hNM : M ≤ N := (le_max_right _ _).trans hN
    apply Erdos66TranslatedDifferencePattern.translatedDiff_of_pattern_budget A M N d h hN3 hNM hd hdN
    intro b hb
    have hh := hP (Erdos66TranslatedDifferencePattern.differenceCode N d b)
    rwa [allTests_translated_difference T N d b hd hb] at hh
  · intro j n hn
    have hn' : max ((cutoff j)^2) (max 1 (max j M)) ≤ n := hn
    have hh := hP (boundaryCode j n)
    rw [allTests_boundary T j n (by omega)] at hh
    exact boundary_count_of_budget A j n M (by omega) (by omega) (by omega) hh
  · intro C h N n z hN hn hz hnz
    have hN' : max (T C) (max 1 (max C (max h M))) ≤ N := hN
    have hh' := hP (tripleCode C h N n z)
    rw [allTests_triple T C h N n z (by omega) hn] at hh'
    exact triple_count_of_budget A C h N n z M (by omega) (by omega) (by omega) (by omega) hn hz hnz hh'

end Erdos66JointTranslatedDifferenceHost
