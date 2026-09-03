import FormalConjecturesUtil

/-! Exact finite counterexamples to two stronger shape properties of survivor
counts. These do not refute a gap-tail estimate or the Jacobsthal conjecture. -/
namespace Erdos970.GapAverages.ShapeExample
open Finset

def count (N a m : ℕ) : ℕ :=
  ((range m).filter (fun i => (a + i + 1).Coprime N)).card

def frequency (N m j : ℕ) : ℕ :=
  ((range N).filter (fun a => count N a m = j)).card

def upperFrequency (N m j : ℕ) : ℕ :=
  ((range N).filter (fun a => j ≤ count N a m)).card

def conditionedUpperFrequency (N m j : ℕ) : ℕ :=
  ((range N).filter (fun a => a.Coprime N ∧ j ≤ count N a m)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exact_count_shapes :
    frequency 210 38 9 = 100 ∧ frequency 210 38 10 = 20 ∧
    frequency 210 38 11 = 4 ∧
    upperFrequency 210 30 8 = 24 ∧ conditionedUpperFrequency 210 30 8 = 6 ∧
    (210 : ℕ).totient = 48 := by
  decide +kernel

/-- The count distribution need not be ultra-log-concave. -/
theorem not_ultra_log_concave :
    ¬frequency 210 38 9 * frequency 210 38 11 * (10 + 1) * (38 - 10 + 1) ≤
      frequency 210 38 10 ^ 2 * 10 * (38 - 10) := by
  rw [exact_count_shapes.1, exact_count_shapes.2.1, exact_count_shapes.2.2.1]
  norm_num

/-- Conditioning the left endpoint to be coprime need not stochastically
reduce the number of survivors in the following interval. -/
theorem not_endpoint_stochastic_domination :
    ¬conditionedUpperFrequency 210 30 8 * 210 ≤
      upperFrequency 210 30 8 * (210 : ℕ).totient := by
  rw [exact_count_shapes.2.2.2.1, exact_count_shapes.2.2.2.2.1,
    exact_count_shapes.2.2.2.2.2]
  norm_num

#print axioms not_ultra_log_concave
#print axioms not_endpoint_stochastic_domination
end Erdos970.GapAverages.ShapeExample
