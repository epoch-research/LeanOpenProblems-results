import FormalConjecturesUtil

/-! Exact integer data for a failed dyadic Laplace inequality. This is an
auxiliary finite computation, not a disproof of the Jacobsthal conjecture. -/
namespace Erdos970.GapAverages.DyadicExample
open Finset

def rawCount (m a : ℕ) : ℕ :=
  ((range m).filter (fun x => x % 3 ≠ a % 3 ∧ x % 7 ≠ a % 7 ∧ x % 11 ≠ a % 11)).card

def weightedSum (m B : ℕ) : ℕ := ∑ a ∈ range 231, 64 ^ (B - rawCount m a)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma count_bounds : ∀ a ∈ range 231, rawCount 26 a ≤ 16 ∧ rawCount 52 a ≤ 30 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma weighted_values : weightedSum 26 16 = 362124420 ∧
    weightedSum 52 30 = 146912027010 := by
  decide +kernel

#print axioms count_bounds
#print axioms weighted_values
end Erdos970.GapAverages.DyadicExample
