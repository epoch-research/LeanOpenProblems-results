import Submission.PolynomialPatternBudgetExplore
import Submission.GeneralCentralTripleMeanExplore
import Submission.BoundaryPairPotentialExplore
import Submission.NaturalPatternRestrictionExplore

/-! Boundary and arbitrary-comparability triple tests are imposed on ONE
harmonic rounding by polynomially encoded positive pattern penalties. -/
namespace Erdos66JointBoundaryTriplePatterns
open Filter AdditiveCombinatorics Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern
  Erdos66PolynomialPatternBudget Erdos66GeneralCentralTripleMean Erdos66BoundaryPairPotential
  Erdos66BoundaryPairMean Erdos66TripleIntersectionGeometry Erdos66TripleIntersectionMean
  Erdos66FiniteRepBernoulli Erdos66Fractional Erdos66BernoulliMatchingPolynomial
  Erdos66Generating Erdos66Rounding Erdos66PowerExceptionalProfile
open scoped Classical Topology
set_option maxHeartbeats 1800000

noncomputable def boundaryPattern (j n : ℕ) : Pattern :=
  matchingPattern n (boundaryPairs n (cutoff j) n) pairCoords ((j:ℝ)+1) (by positivity)
noncomputable def triplePattern (N n z : ℕ) : Pattern :=
  matchingPattern (max n z) (triples (max n z) N n z) coords (tilt N) (tilt_nonneg N)

def boundaryCode (j n : ℕ) : ℕ := Nat.pair 0 (Nat.pair j n)
def tripleCode (C h N n z : ℕ) : ℕ := Nat.pair 1 (Nat.pair C (Nat.pair h (Nat.pair N (Nat.pair n z))))

noncomputable def tests (T : ℕ → ℕ) (m : ℕ) : Pattern :=
  let q := Nat.unpair m
  if q.1=0 then
    let r := Nat.unpair q.2
    if (cutoff r.1)^2 ≤ r.2 then boundaryPattern r.1 r.2 else zeroPattern
  else if q.1=1 then
    let r := Nat.unpair q.2
    let s := Nat.unpair r.2
    let u := Nat.unpair s.2
    let v := Nat.unpair u.2
    if T r.1 ≤ u.1 ∧ v.1 ≤ r.1*u.1 then triplePattern u.1 v.1 v.2 else zeroPattern
  else zeroPattern

lemma tests_boundary (T : ℕ → ℕ) (j n : ℕ) (hn : (cutoff j)^2 ≤ n) :
    tests T (boundaryCode j n)=boundaryPattern j n := by
  simp only [tests,boundaryCode,Nat.unpair_pair,if_true,if_pos hn]

lemma tests_triple (T : ℕ → ℕ) (C h N n z : ℕ) (hN : T C ≤ N) (hn : n ≤ C*N) :
    tests T (tripleCode C h N n z)=triplePattern N n z := by
  simp only [tests,tripleCode,Nat.unpair_pair,show ¬(1:ℕ)=0 by omega,if_false,if_true,hN,hn,and_self]

lemma boundaryPattern_mean (j n : ℕ) (hn : (cutoff j)^2 ≤ n) :
    (boundaryPattern j n).eval profile ≤ 3*((n:ℝ)+1) := by
  rw [boundaryPattern,matchingPattern_eval]
  apply (boundary_raw_mean n j n hn).trans
  have he : Real.exp 1 ≤ (3:ℝ) := by linarith [Real.exp_one_lt_d9]
  exact mul_le_mul_of_nonneg_right he (by positivity)

lemma triplePattern_mean (T : ℕ → ℕ)
    (hT : ∀ C N, T C ≤ N → ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ profile i.val) ≤ Real.exp 1)
    (C N n z : ℕ) (hN : T C ≤ N) (hn : n ≤ C*N) :
    (triplePattern N n z).eval profile ≤ 3 := by
  rw [triplePattern,matchingPattern_eval]
  exact (hT C N hN _ n z hn).trans (by linarith [Real.exp_one_lt_d9])

lemma tests_mean (T : ℕ → ℕ)
    (hT : ∀ C N, T C ≤ N → ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ profile i.val) ≤ Real.exp 1)
    (m : ℕ) : (tests T m).eval profile ≤ 3*((m:ℝ)+2) := by
  dsimp only [tests]
  split_ifs with htag hactive htag' hactive'
  · apply (boundaryPattern_mean _ _ hactive).trans
    have hn := (Nat.unpair_right_le (Nat.unpair m).2).trans (Nat.unpair_right_le m)
    have hn' : (((Nat.unpair (Nat.unpair m).2).2:ℕ):ℝ) ≤ m := by exact_mod_cast hn
    linarith
  · simp only [zeroPattern_eval]; positivity
  · apply (triplePattern_mean T hT _ _ _ _ hactive'.1 hactive'.2).trans
    linarith [Nat.cast_nonneg (α := ℝ) m]
  · simp only [zeroPattern_eval]; positivity
  · simp only [zeroPattern_eval]; positivity

 theorem exists_joint_pattern_bounds : ∃ (A : Set ℕ) (M : ℕ) (T : ℕ → ℕ),
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) ∧
    (∀ j n, (cutoff j)^2 ≤ n → (boundaryPattern j n).value (fun i ↦ decide (i∈A)) ≤
      ((boundaryCode j n:ℝ)+M+2)^4) ∧
    (∀ C h N n z, T C ≤ N → n ≤ C*N → (triplePattern N n z).value (fun i ↦ decide (i∈A)) ≤
      ((tripleCode C h N n z:ℝ)+M+2)^4) := by
  have hcut (C : ℕ) : ∃ T : ℕ, ∀ N≥T, ∀ L n z, n ≤ C*N →
      matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ profile i.val) ≤ Real.exp 1 :=
    eventually_atTop.mp (eventually_comparable_poly_mean C)
  choose T hT using hcut
  obtain ⟨A,M,hbr,hP,hcost⟩ := exists_polynomial_pattern_bounds (tests T) (tests_mean T hT)
  refine ⟨A,M,T,hbr,hcost,?_,?_⟩
  · intro j n hn
    have hh := hP (boundaryCode j n)
    rwa [tests_boundary T j n hn] at hh
  · intro C h N n z hN hn
    have hh := hP (tripleCode C h N n z)
    rwa [tests_triple T C h N n z hN hn] at hh

end Erdos66JointBoundaryTriplePatterns
