import Submission.GeneralPatternPowerExplore
import Submission.HostPatternMeanExplore
import Submission.JointBoundaryTriplePatternsExplore
import Submission.GeneralCentralTripleMeanExplore
import Submission.BoundaryPairPotentialExplore
import Submission.NaturalPatternRestrictionExplore

/-! Boundary and arbitrary-comparability triple tests are imposed on ONE
harmonic rounding by polynomially encoded positive pattern penalties. -/
namespace Erdos66HostPatternSelection
open Filter AdditiveCombinatorics Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern
  Erdos66GeneralPatternPower Erdos66HostPatternMean Erdos66JointBoundaryTriplePatterns Erdos66GeneralCentralTripleMean Erdos66BoundaryPairPotential
  Erdos66BoundaryPairMean Erdos66TripleIntersectionGeometry Erdos66TripleIntersectionMean
  Erdos66FiniteRepBernoulli Erdos66Fractional Erdos66BernoulliMatchingPolynomial
  Erdos66Generating Erdos66Rounding Erdos66PowerExceptionalProfile
open scoped Classical Topology
set_option maxHeartbeats 1800000

noncomputable def hostBoundaryPattern (j n : ℕ) : Pattern :=
  matchingPattern n (boundaryPairs n (hostCutoff j) n) pairCoords ((j:ℝ)+1) (by positivity)
noncomputable def hostTests (T : ℕ → ℕ) (m : ℕ) : Pattern :=
  let q := Nat.unpair m
  if q.1=0 then
    let r := Nat.unpair q.2
    if (hostCutoff r.1)^2 ≤ r.2 then hostBoundaryPattern r.1 r.2 else zeroPattern
  else if q.1=1 then
    let r := Nat.unpair q.2
    let s := Nat.unpair r.2
    let u := Nat.unpair s.2
    let v := Nat.unpair u.2
    if T r.1 ≤ u.1 ∧ v.1 ≤ r.1*u.1 then triplePattern u.1 v.1 v.2 else zeroPattern
  else zeroPattern

lemma hostTests_boundary (T : ℕ → ℕ) (j n : ℕ) (hn : (hostCutoff j)^2 ≤ n) :
    hostTests T (boundaryCode j n)=hostBoundaryPattern j n := by
  simp only [hostTests,boundaryCode,Nat.unpair_pair,if_true,if_pos hn]

lemma hostTests_triple (T : ℕ → ℕ) (C h N n z : ℕ) (hN : T C ≤ N) (hn : n ≤ C*N) :
    hostTests T (tripleCode C h N n z)=triplePattern N n z := by
  simp only [hostTests,tripleCode,Nat.unpair_pair,show ¬(1:ℕ)=0 by omega,if_false,if_true,hN,hn,and_self]

lemma hostBoundaryPattern_mean (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hdom : ∀ i, p i ≤ 32*profile i) (j n : ℕ) (hn : (hostCutoff j)^2 ≤ n) :
    (hostBoundaryPattern j n).eval p ≤ 3*((n:ℝ)+1) := by
  rw [hostBoundaryPattern,matchingPattern_eval]
  apply (host_boundary_raw_mean p hp hdom n j n hn).trans
  have he : Real.exp 1 ≤ (3:ℝ) := by linarith [Real.exp_one_lt_d9]
  exact mul_le_mul_of_nonneg_right he (by positivity)

lemma hostTriplePattern_mean (p : ℕ → ℝ) (T : ℕ → ℕ)
    (hT : ∀ C N, T C ≤ N → ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ p i.val) ≤ Real.exp 1)
    (C N n z : ℕ) (hN : T C ≤ N) (hn : n ≤ C*N) :
    (triplePattern N n z).eval p ≤ 3 := by
  rw [triplePattern,matchingPattern_eval]
  exact (hT C N hN _ n z hn).trans (by linarith [Real.exp_one_lt_d9])

lemma hostTests_mean (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hdom : ∀ i, p i ≤ 32*profile i) (T : ℕ → ℕ)
    (hT : ∀ C N, T C ≤ N → ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ p i.val) ≤ Real.exp 1)
    (m : ℕ) : (hostTests T m).eval p ≤ 3*((m:ℝ)+2) := by
  dsimp only [hostTests]
  split_ifs with htag hactive htag' hactive'
  · apply (hostBoundaryPattern_mean p hp hdom _ _ hactive).trans
    have hn := (Nat.unpair_right_le (Nat.unpair m).2).trans (Nat.unpair_right_le m)
    have hn' : (((Nat.unpair (Nat.unpair m).2).2:ℕ):ℝ) ≤ m := by exact_mod_cast hn
    linarith
  · simp only [zeroPattern_eval]; positivity
  · apply (hostTriplePattern_mean p T hT _ _ _ _ hactive'.1 hactive'.2).trans
    linarith [Nat.cast_nonneg (α := ℝ) m]
  · simp only [zeroPattern_eval]; positivity
  · simp only [zeroPattern_eval]; positivity

 theorem exists_host_pattern_bounds (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hdom : ∀ i, p i ≤ 32*profile i)
    (hconv : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 (1024:ℝ))) : ∃ (A : Set ℕ) (M : ℕ) (T : ℕ → ℕ),
    (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1024 (1/((j:ℝ)+1)) n (sumRep A n))) ∧
    (∀ j n, (hostCutoff j)^2 ≤ n → (hostBoundaryPattern j n).value (fun i ↦ decide (i∈A)) ≤
      ((boundaryCode j n:ℝ)+M+2)^4) ∧
    (∀ C h N n z, T C ≤ N → n ≤ C*N → (triplePattern N n z).value (fun i ↦ decide (i∈A)) ≤
      ((tripleCode C h N n z:ℝ)+M+2)^4) := by
  have hcut (C : ℕ) : ∃ T : ℕ, ∀ N≥T, ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ p i.val) ≤ Real.exp 1 :=
    eventually_atTop.mp (eventually_host_triple_mean p (fun i ↦ (hp i).1) hdom C)
  choose T hT using hcut
  obtain ⟨A,M,hbr,hP,hcost⟩ := exists_general_polynomial_patterns p hp 1024 (by norm_num) hconv (hostTests T)
    (hostTests_mean p (fun i ↦ (hp i).1) hdom T hT)
  refine ⟨A,M,T,hbr,hcost,?_,?_⟩
  · intro j n hn
    have hh := hP (boundaryCode j n)
    rwa [hostTests_boundary T j n hn] at hh
  · intro C h N n z hN hn
    have hh := hP (tripleCode C h N n z)
    rwa [hostTests_triple T C h N n z hN hn] at hh

end Erdos66HostPatternSelection
