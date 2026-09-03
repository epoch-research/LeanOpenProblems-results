import Submission.RarePatternCodeGrowthExplore

/-! ONE harmonic rounding with arbitrarily small boundary coefficients and
bounded central triples for all fixed comparability factors and polynomial
horizons. The constants are deliberately generous. -/
namespace Erdos66JointBoundaryTripleCounts
open AdditiveCombinatorics Erdos66JointBoundaryTriplePatterns Erdos66RarePatternCodeGrowth
  Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern Erdos66NaturalPatternRestriction
  Erdos66BoundaryPairCounts Erdos66BoundaryPairMean Erdos66BoundaryPairPotential
  Erdos66DisjointMatchingPolynomial Erdos66BernoulliMatchingPolynomial
  Erdos66CentralTripleCounts Erdos66TripleIntersectionGeometry Erdos66TripleIntersectionMean
  Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66Generating Erdos66Rounding Erdos66PowerExceptionalProfile
open scoped Classical
set_option maxHeartbeats 2200000

lemma boundaryPattern_value (A : Set ℕ) (j n : ℕ) :
    (boundaryPattern j n).value (fun i ↦ decide (i∈A))=
      Real.exp (((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ)) := by
  rw [boundaryPattern,Pattern.value,matchingPattern_eval]
  change matchingPoly (boundaryPairs n (cutoff j) n) pairCoords ((j:ℝ)+1)
    (fun i ↦ bit (restrict A n i))=_
  rw [matchingPoly_binary_disjoint _ _ (boundaryPairs_disjoint n (cutoff j) n),
    selected_boundary_card n (cutoff j) n (cutoff_ge_two j),boundary_restrict A n (cutoff j) n le_rfl]

lemma boundary_count_of_budget (A : Set ℕ) (j n M : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) (hM : M ≤ n)
    (hbudget : (boundaryPattern j n).value (fun i ↦ decide (i∈A)) ≤ ((boundaryCode j n:ℝ)+M+2)^4) :
    ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤ 20*Real.log ((n:ℝ)+1) := by
  rw [boundaryPattern_value] at hbudget
  have hcode : (boundaryCode j n:ℝ)+M+2 ≤ ((n:ℝ)+1)^5 :=
    by exact_mod_cast boundaryCode_shift_bound j n M hn hj hM
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (boundaryCode j n:ℝ)+M+2) hcode 4
  have hh := Real.log_le_log (Real.exp_pos _) (hbudget.trans hpow)
  rw [Real.log_exp,Real.log_pow,Real.log_pow] at hh
  norm_num at hh
  linarith only [hh]

noncomputable def tripleCap (h : ℕ) : ℕ := 144*(32*(h+2)+1)+2

lemma triple_count_of_budget (A : Set ℕ) (C h N n z M : ℕ) (hN : 1 ≤ N) (hC : C ≤ N)
    (hh : h ≤ N) (hM : M ≤ N) (hn : n ≤ C*N) (hz : z ≤ N^h) (hnz : n≠z)
    (hbudget : (triplePattern N n z).value (fun i ↦ decide (i∈A)) ≤
      ((tripleCode C h N n z:ℝ)+M+2)^4) : (fiber A N n z).card ≤ tripleCap h := by
  let L := max n z
  let r := 32*(h+2)+1
  let k := 16*r
  have ht := tilt_pos (show 0<N by omega)
  have hcode : (tripleCode C h N n z:ℝ)+M+2 ≤ ((N:ℝ)+1)^r :=
    by exact_mod_cast tripleCode_shift_bound C h N n z M hN hC hh hM hn hz
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (tripleCode C h N n z:ℝ)+M+2) hcode 4
  have hexp : Real.exp (tilt N*(k:ℝ))=(((N:ℝ)+1)^r)^4 := by
    have he : tilt N*(k:ℝ)=((r*4:ℕ):ℝ)*Real.log ((N:ℝ)+1) := by
      dsimp only [tilt,k]
      push_cast
      ring
    rw [he,Real.exp_nat_mul,Real.exp_log (by positivity),pow_mul]
  rw [triplePattern,Pattern.value,matchingPattern_eval] at hbudget
  have hp : matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ bit (restrict A L i)) <
      Real.exp (tilt N*((k:ℝ)+1)) := by
    apply (hbudget.trans hpow).trans_lt
    rw [←hexp]
    apply Real.exp_lt_exp.mpr
    nlinarith only [ht]
  have hdeg : ∀ e∈triples L N n z,
      ((triples L N n z).filter (fun f ↦ ¬Disjoint (coords e) (coords f))).card ≤ 9 := by
    intro e he
    exact conflict_card L N n z e
  have hreal := matchingPoly_bounds_realized (triples L N n z) coords 9 k
    (fun e _ ↦ coords_nonempty e) (by
      intro e he
      convert hdeg e he using 1
      congr 1
      ext f
      simp only [Finset.mem_filter]) (tilt N) ht (restrict A L) hp
  have hfib := selected_fiber_bound L N n z (9*k) (restrict A L) hnz hreal
  rw [fiber_restrict A L N n z (le_max_left _ _) (le_max_right _ _)] at hfib
  dsimp only [k,r,tripleCap] at hfib ⊢
  omega

 theorem exists_joint_boundary_triple_rounding : ∃ (A : Set ℕ) (NB : ℕ → ℕ) (NT : ℕ → ℕ → ℕ),
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) ∧
    (∀ j n, NB j ≤ n → ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤ 20*Real.log ((n:ℝ)+1)) ∧
    (∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
      (fiber A N n z).card ≤ tripleCap h) := by
  obtain ⟨A,M,T,hbr,hcost,hB,hT⟩ := exists_joint_pattern_bounds
  let NB : ℕ → ℕ := fun j ↦ max ((cutoff j)^2) (max 1 (max j M))
  let NT : ℕ → ℕ → ℕ := fun C h ↦ max (T C) (max 1 (max C (max h M)))
  refine ⟨A,NB,NT,hbr,hcost,?_,?_⟩
  · intro j n hn
    have hn' : max ((cutoff j)^2) (max 1 (max j M)) ≤ n := hn
    exact boundary_count_of_budget A j n M (by omega) (by omega) (by omega) (hB j n (by omega))
  · intro C h N n z hN hn hz hnz
    have hN' : max (T C) (max 1 (max C (max h M))) ≤ N := hN
    exact triple_count_of_budget A C h N n z M (by omega) (by omega) (by omega) (by omega) hn hz hnz
      (hT C h N n z (by omega) hn)

end Erdos66JointBoundaryTripleCounts
