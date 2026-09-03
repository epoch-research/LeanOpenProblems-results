import FormalConjecturesUtil

/-! A finite mass-partition model. It shows that symmetric subcritical selection
moments do not, by themselves, force a balanced comparison of largest parts.
This is not a counterexample involving `Nat.maxPrimeFac`. -/

namespace Erdos371RestrictedMoments

abbrev State := Fin 7

def parts : State → List ℕ :=
  ![[5], [4,1], [3,2], [3,1,1], [2,2,1], [2,1,1,1], [1,1,1,1,1]]

def base : State → ℤ := ![24,30,20,20,15,10,1]

def perturb : Matrix State State ℤ := !![
  0, 0, 0, 0, 0, 0, 0;
  0, 0, -6, 6, 9, -12, 3;
  0, 6, 0, -8, -3, 6, -1;
  0, -6, 8, 0, -9, 10, -3;
  0, -9, 3, 9, 0, -3, 0;
  0, 12, -6, -10, 3, 0, 1;
  0, -3, 1, 3, 0, -1, 0]

def weight (i j : State) : ℤ := base i * base j + perturb i j

def selections : List (List ℕ) :=
  [[],[1],[2],[1,1],[3],[2,1],[1,1,1],[4],[3,1],[2,2],[2,1,1],
    [1,1,1,1],[5],[4,1],[3,2],[3,1,1],[2,2,1],[2,1,1,1],[1,1,1,1,1]]

def feature (u : List ℕ) (i : State) : ℤ :=
  ∏ k ∈ Finset.Icc 1 5, (Nat.choose ((parts i).count k) (u.count k) : ℤ)

def largest : State → ℕ := ![5,4,3,3,2,2,1]

lemma states_have_mass_five : ∀ i, (parts i).sum = 5 := by decide +kernel
lemma weight_nonneg : ∀ i j, 0 ≤ weight i j := by decide +kernel
lemma total_weight : (∑ i : State, ∑ j : State, weight i j) = 14400 := by decide +kernel
lemma equal_marginals : ∀ i : State,
    (∑ j : State, weight i j) = 120 * base i ∧
    (∑ j : State, weight j i) = 120 * base i := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma subcritical_moments : ∀ u ∈ selections, ∀ v ∈ selections,
    u.sum + v.sum ≤ 5 →
      (∑ i : State, ∑ j : State, weight i j * feature u i * feature v j) =
      (∑ i : State, base i * feature u i) * (∑ j : State, base j * feature v j) := by
  decide +kernel

lemma largest_comparison_biased :
    (∑ i : State, ∑ j : State, weight i j *
      (if largest i > largest j then 1 else if largest i < largest j then -1 else 0)) = 2 := by
  decide +kernel

end Erdos371RestrictedMoments

#print axioms Erdos371RestrictedMoments.subcritical_moments
#print axioms Erdos371RestrictedMoments.largest_comparison_biased
