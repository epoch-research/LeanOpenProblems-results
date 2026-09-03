import Submission.ExactBracketPatternCostsExplore
import Submission.JointBoundaryTripleCountsExplore

/-! One host simultaneously satisfies exact harmonic brackets, all power-cost
rows, arbitrarily small boundary coefficients, and bounded central triples. -/
namespace Erdos66ExactBracketPatternHost
open Filter AdditiveCombinatorics Erdos66ExactBracketPatternCosts
  Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern
  Erdos66PrefixBalancedPowerProfile Erdos66PowerExceptionalProfile Erdos66Fractional
  Erdos66Generating Erdos66Rounding Erdos66ClampedPrefixContinuation
  Erdos66PolynomialPatternBudget Erdos66JointBoundaryTriplePatterns
  Erdos66GeneralCentralTripleMean Erdos66BoundaryPairPotential
  Erdos66BoundaryPairMean Erdos66TripleIntersectionGeometry Erdos66TripleIntersectionMean
  Erdos66FiniteRepBernoulli Erdos66BernoulliMatchingPolynomial
  Erdos66JointBoundaryTripleCounts Erdos66BoundaryPairCounts Erdos66CentralTripleCounts
open scoped Classical Topology
set_option maxHeartbeats 2200000

 theorem exists_pattern_sparse_power_potentials (P : ℕ → Pattern)
    (hP : ∀ S : Finset ℕ, (∑ j∈S, (P j).eval profile) ≤ 1/4) :
    ∃ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) ∧
      (∀ S : Finset ℕ, (∑ j∈S, (P j).value (fun i ↦ decide (i∈A))) ≤ 1) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) := by
  obtain ⟨A,hbr,hpat,hcost⟩ := exists_pattern_sparse_summable_rep_costs P hP
    (fun j n x ↦ powerCost 1 (1/((j:ℝ)+1)) n x)
    (fun j n ↦ powerTail 1 (1/((j:ℝ)+1)) n)
    (fun j n b ↦ powerWeight 1 (1/((j:ℝ)+1)) n b)
    (fun j _n b ↦ powerTilt (1/((j:ℝ)+1)) b)
    (fun j n b ↦ powerWeight_nonneg _ _ _ _)
    (fun j n b ↦ powerTilt_bound _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])) b)
    (fun j n x ↦ powerCost_expansion _ _ _ _)
    (fun j ↦ powerTail_summable _ _ (by norm_num) (by positivity))
    (fun j ↦ uniform_powerCost_bound profile (fun n ↦ ⟨profile_nonneg n,profile_le_one n⟩)
      1 (by norm_num) profile_log_limit _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])))
  exact ⟨A,hbr,hpat,hcost⟩

 theorem exists_indexed_pattern_power_potentials {α : Type*} [Denumerable α] (P : α → Pattern)
    (hP : ∀ S : Finset α, (∑ j∈S, (P j).eval profile) ≤ 1/4) :
    ∃ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) ∧
      (∀ S : Finset α, (∑ j∈S, (P j).value (fun i ↦ decide (i∈A))) ≤ 1) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) := by
  let e := Denumerable.eqv α
  have hnat (S : Finset ℕ) : (∑ j∈S, (P (e.symm j)).eval profile) ≤ 1/4 := by
    have hh := hP (S.image e.symm)
    rw [Finset.sum_image e.symm.injective.injOn] at hh
    exact hh
  obtain ⟨A,hbr,hpat,hcost⟩ := exists_pattern_sparse_power_potentials (fun n ↦ P (e.symm n)) hnat
  refine ⟨A,hbr,?_,hcost⟩
  intro S
  have hh := hpat (S.image e)
  rw [Finset.sum_image e.injective.injOn] at hh
  simpa only [Equiv.symm_apply_apply] using hh


 theorem exists_polynomial_pattern_bounds (P : ℕ → Pattern)
    (hP : ∀ m, (P m).eval profile ≤ 3*((m:ℝ)+2)) :
    ∃ (A : Set ℕ) (M : ℕ),
      (∀ L, PrefixBrackets profile A L) ∧
      (∀ m, (P m).value (fun i ↦ decide (i∈A)) ≤ ((m:ℝ)+M+2)^4) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) := by
  obtain ⟨M,hM⟩ := exists_index_tail_budget
  let Q : ℕ → Pattern := fun m ↦ scalePattern (1/((m:ℝ)+M+2)^4) (by positivity) (P m)
  have hQ (S : Finset ℕ) : (∑ m∈S, (Q m).eval profile) ≤ 1/4 := by
    apply (Finset.sum_le_sum (fun m hm ↦ ?_)).trans (hM S).le
    dsimp only [Q]
    rw [scalePattern_eval]
    have hx : 0 < (m:ℝ)+M+2 := by positivity
    calc
      _ ≤ (1/((m:ℝ)+M+2)^4)*(3*((m:ℝ)+2)) :=
        mul_le_mul_of_nonneg_left (hP m) (by positivity)
      _ ≤ (1/((m:ℝ)+M+2)^4)*(3*((m:ℝ)+M+2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [Nat.cast_nonneg (α := ℝ) M]
      _ = 3/((m:ℝ)+M+2)^3 := by field_simp
  obtain ⟨A,hbr,hbounds,hcost⟩ := exists_pattern_sparse_power_potentials Q hQ
  refine ⟨A,M,hbr,?_,hcost⟩
  intro m
  have hh := hbounds {m}
  simp only [Finset.sum_singleton,Q,scalePattern_value] at hh
  have hx : 0 < ((m:ℝ)+M+2)^4 := by positivity
  rw [one_div,mul_comm,←div_eq_mul_inv] at hh
  exact (div_le_one hx).mp hh


 theorem exists_joint_pattern_bounds : ∃ (A : Set ℕ) (M : ℕ) (T : ℕ → ℕ),
    (∀ L, PrefixBrackets profile A L) ∧
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


 theorem exists_joint_boundary_triple_rounding : ∃ (A : Set ℕ) (NB : ℕ → ℕ) (NT : ℕ → ℕ → ℕ),
    (∀ L, PrefixBrackets profile A L) ∧
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


end Erdos66ExactBracketPatternHost
