import FormalConjecturesUtil
import Submission.RestrictedMoments

/-! An exact bounded-density coupling of the seven partitions of five.
Its marginals are the cycle-partition law of a uniform permutation of five
letters, and its subcritical selection moments match independence. Its largest-
part comparison is nevertheless biased. This is a finite model statement,
NOT an arithmetic counterexample or a Poisson--Dirichlet limit assertion. -/

namespace Erdos371BoundedMomentCoupling

open Finset
open Erdos371RestrictedMoments (State parts base selections feature largest)

/-- Nontrivial cycles; the omitted one-cycles are determined by total mass five. -/
def nontrivialType (i : State) : Multiset ℕ :=
  ↑((parts i).filter (fun k => 2 ≤ k))

/-- The model's given integer weights really count the seven cycle types in S₅. -/
lemma base_is_permutation_count (i : State) :
    ((({g : Equiv.Perm (Fin 5) | g.cycleType = nontrivialType i} : Finset (Equiv.Perm (Fin 5))).card):ℤ) = base i := by
  rw [Equiv.Perm.card_of_cycleType]
  fin_cases i <;> decide +kernel

/-- This matrix is 36 times a feasible rational perturbation of the product law. -/
def perturb : Matrix State State ℤ := !![
  0, 25380, -2688, -17280, -12690, 7260, 18;
  -25380, 0, 21600, 3360, 4365, -4320, 375;
  2688, -21600, 0, 12760, 10800, -4260, -388;
  17280, -3360, -12760, 0, -4140, 3700, -720;
  12690, -4365, -10800, 4140, 0, -2205, 540;
  -7260, 4320, 4260, -3700, 2205, 0, 175;
  -18, -375, 388, 720, -540, -175, 0]

def weight (i j : State) : ℤ := 36*base i*base j+perturb i j

def marginal (i : State) : ℚ := (base i:ℚ)/120

def probability (i j : State) : ℚ := (weight i j:ℚ)/518400

lemma weight_bounds : ∀ i j : State, 0 ≤ weight i j ∧ weight i j ≤ 72*base i*base j := by
  decide +kernel

lemma total_weight : (∑ i : State, ∑ j : State, weight i j) = 518400 := by
  decide +kernel

lemma weight_marginals : ∀ i : State,
    (∑ j : State, weight i j) = 4320*base i ∧
    (∑ j : State, weight j i) = 4320*base i := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma subcritical_weight_moments : ∀ u ∈ selections, ∀ v ∈ selections,
    u.sum+v.sum ≤ 5 →
      (∑ i : State, ∑ j : State, weight i j*feature u i*feature v j) =
        36*(∑ i : State, base i*feature u i)*(∑ j : State, base j*feature v j) := by
  decide +kernel

lemma probability_bounds : ∀ i j : State,
    0 ≤ probability i j ∧ probability i j ≤ 2*marginal i*marginal j := by
  decide +kernel

lemma probability_sum : (∑ i : State, ∑ j : State, probability i j) = 1 := by
  decide +kernel

lemma probability_marginals : ∀ i : State,
    (∑ j : State, probability i j) = marginal i ∧
    (∑ j : State, probability j i) = marginal i := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma subcritical_probability_moments : ∀ u ∈ selections, ∀ v ∈ selections,
    u.sum+v.sum ≤ 5 →
      (∑ i : State, ∑ j : State, probability i j*(feature u i:ℚ)*(feature v j:ℚ)) =
        (∑ i : State, marginal i*(feature u i:ℚ)) *
        (∑ j : State, marginal j*(feature v j:ℚ)) := by
  decide +kernel

/-- The nonzero signed expectation is checked exactly, not inferred from an LP solver. -/
theorem largest_comparison_biased :
    (∑ i : State, ∑ j : State, probability i j*
      (if largest i>largest j then 1 else if largest i<largest j then -1 else 0)) =
      (31087/259200:ℚ) := by
  decide +kernel

/-- Independence of these specified moments and a bounded coupling density do
not force zero signed comparison in this finite permutation-partition model. -/
theorem bounded_density_moment_obstruction :
    ∃ w : State → State → ℚ,
      (∀ i j, 0 ≤ w i j ∧ w i j ≤ 2*marginal i*marginal j) ∧
      (∀ i, (∑ j, w i j)=marginal i ∧ (∑ j, w j i)=marginal i) ∧
      (∀ u ∈ selections, ∀ v ∈ selections, u.sum+v.sum ≤ 5 →
        (∑ i, ∑ j, w i j*(feature u i:ℚ)*(feature v j:ℚ)) =
          (∑ i, marginal i*(feature u i:ℚ))*(∑ j, marginal j*(feature v j:ℚ))) ∧
      (∑ i, ∑ j, w i j*
        (if largest i>largest j then 1 else if largest i<largest j then -1 else 0)) =
        31087/259200 := by
  exact ⟨probability,probability_bounds,probability_marginals,
    subcritical_probability_moments,largest_comparison_biased⟩

end Erdos371BoundedMomentCoupling

#print axioms Erdos371BoundedMomentCoupling.base_is_permutation_count
#print axioms Erdos371BoundedMomentCoupling.bounded_density_moment_obstruction
