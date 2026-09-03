import FormalConjecturesUtil

/-! Arithmetic for a parallel-block obstruction to an auxiliary Best-leaf
vertex-loss rule. These lemmas do not construct graphs or prove the claimed
block profile, and do not settle Erdős 184. -/
namespace Erdos184Work.ParallelLeafArithmetic

/-- If all non-central pieces cost at least twelve per block pair, and each
central cycle consumes two central edges, the total cost is at least 13q+1. -/
lemma lower_budget (q cycles singles pieces : ℕ)
    (hdegree : 2 * cycles + singles = 2 * q + 1)
    (hpieces : 12 * q + cycles + singles ≤ pieces) :
    13 * q + 1 ≤ pieces := by omega

/-- Upper budget when the central closing edge is absent. -/
lemma no_closing_budget (q heavy : ℕ) (hh : heavy ≤ 2 * q) :
    12 * q + (heavy + 1) / 2 ≤ 13 * q := by omega

/-- A light block or missing connector saves one full unit from the source
budget even when the closing edge is present. -/
lemma light_block_budget (q heavy : ℕ) (hh : heavy < 2 * q) :
    12 * q + heavy / 2 + 1 ≤ 13 * q := by omega

/-- When all blocks are heavy, a proper block's path-cofactor saving supplies
that unit instead. -/
lemma proper_heavy_budget (q pieces : ℕ)
    (hpieces : pieces + 1 ≤ 12 * q + (2 * q) / 2 + 1) :
    pieces ≤ 13 * q := by omega

lemma explicit_partition_budget (q : ℕ) :
    8 * q + (5 * q + 1) = 13 * q + 1 := by omega

lemma deletion_loss (q : ℕ) :
    (13 * q + 1) - 12 * q = q + 1 := by omega

/-- These candidate source counts are still linear, not a counterexample to
the conjecture in Spec.lean. -/
lemma source_cost_linear (q : ℕ) :
    13 * q + 1 ≤ 2 * (12 * q + 2) := by omega

end Erdos184Work.ParallelLeafArithmetic
#print axioms Erdos184Work.ParallelLeafArithmetic.lower_budget
#print axioms Erdos184Work.ParallelLeafArithmetic.light_block_budget
#print axioms Erdos184Work.ParallelLeafArithmetic.deletion_loss
