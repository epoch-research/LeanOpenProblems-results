import Submission.GreedyCoverOrder

/-!
Two finite obstructions to proposed estimates for canonical greedy orders.
They do not refute an amortized sorting bound or the Jacobsthal conjecture.
All computations below are checked by the Lean kernel.
-/
namespace Erdos970.GreedyCoverOrder.SortingObstruction
open Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Greedy endpoint within a finite test window. -/
def endpoint (m : ℕ) (l : List ℕ) : ℕ :=
  firstPosition (greedyResidual (range m) l)

def beforeSwap : List ℕ := [5, 3, 2, 7]
def afterSwap : List ℕ := [5, 2, 3, 7]

theorem adjacent_swap_data :
    beforeSwap.Nodup ∧ afterSwap.Nodup ∧
    (∀ p ∈ beforeSwap, p.Prime) ∧ (∀ p ∈ afterSwap, p.Prime) ∧
    beforeSwap.Perm afterSwap ∧
    endpoint 100 beforeSwap = 9 ∧ endpoint 100 afterSwap = 6 ∧
    (greedyResidual (range 100) beforeSwap).Nonempty ∧
    (greedyResidual (range 100) afterSwap).Nonempty := by
  decide +kernel

/-- Even an adjacent inverted pair can lose more than two positions when sorted. -/
theorem adjacent_swap_loss_gt_two :
    endpoint 100 afterSwap + 2 < endpoint 100 beforeSwap := by
  have h := adjacent_swap_data
  rw [h.2.2.2.2.2.1, h.2.2.2.2.2.2.1]
  norm_num

/-- The false local claim is negated explicitly; no universal constant bound
or amortized estimate is refuted by this four-prime example. -/
theorem no_two_position_adjacent_loss : ¬ (∀ (a b : List ℕ) (p q m : ℕ),
    (a ++ p :: q :: b).Nodup → (∀ u ∈ a ++ p :: q :: b, u.Prime) → q < p →
    (greedyResidual (range m) (a ++ p :: q :: b)).Nonempty →
    (greedyResidual (range m) (a ++ q :: p :: b)).Nonempty →
    endpoint m (a ++ p :: q :: b) ≤ endpoint m (a ++ q :: p :: b) + 2) := by
  intro h
  have hd := adjacent_swap_data
  have hh := h [5] [7] 3 2 100 hd.1 hd.2.2.1 (by norm_num)
    hd.2.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.2
  exact (not_le_of_gt adjacent_swap_loss_gt_two) hh

def firstSeven : List ℕ := [2, 3, 5, 7, 11, 13, 17]
def shiftedSeven : List ℕ := [2, 3, 7, 11, 13, 17, 19]

theorem increasing_lists_data :
    firstSeven.Pairwise (· < ·) ∧ shiftedSeven.Pairwise (· < ·) ∧
    (∀ p ∈ firstSeven, p.Prime) ∧ (∀ p ∈ shiftedSeven, p.Prime) ∧
    List.Forall₂ (· ≤ ·) firstSeven shiftedSeven ∧
    firstSeven.length = 7 ∧ shiftedSeven.length = 7 ∧
    endpoint 100 firstSeven = 17 ∧ endpoint 100 shiftedSeven = 21 ∧
    (greedyResidual (range 100) firstSeven).Nonempty ∧
    (greedyResidual (range 100) shiftedSeven).Nonempty := by
  decide +kernel

/-- Increasing every coordinate of an increasing prime list can increase its
canonical greedy endpoint. This is not a statement about the maximal endpoint
over all permutations of either prime set. -/
theorem increasing_prime_replacement_gains :
    endpoint 100 firstSeven < endpoint 100 shiftedSeven := by
  have h := increasing_lists_data
  rw [h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1]
  norm_num

#print axioms adjacent_swap_data
#print axioms no_two_position_adjacent_loss
#print axioms increasing_lists_data
#print axioms increasing_prime_replacement_gains
end Erdos970.GreedyCoverOrder.SortingObstruction
