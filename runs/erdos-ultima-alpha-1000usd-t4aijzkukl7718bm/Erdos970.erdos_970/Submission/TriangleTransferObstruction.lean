import Submission.TriangleMultipliers

/-! Triangle incompatibility need not persist when primes increase. -/
namespace Erdos970.PatternPacking.TriangleTransferObstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def oldFamily : Finset (Finset ℕ) := {{3, 7}, {3, 11}, {7, 11}}
def newFamily : Finset (Finset ℕ) := {{3, 7}, {3, 13}, {7, 13}}

theorem old_no_triangle : NoTriangle 14 oldFamily := by decide +kernel

theorem old_card_le_two (r : ℕ → ℕ) : patternCount 14 oldFamily r ≤ 2 := by
  apply patternCount_le_two_of_noTriangle 14 oldFamily _ old_no_triangle r
  decide +kernel

/-- Positions 0,6,13 respectively hit {3,13}, {3,7}, {7,13}. -/
theorem new_has_three :
    3 ≤ patternCount 14 newFamily (fun p => if p = 7 then 6 else 0) := by
  decide +kernel

theorem new_not_no_triangle : ¬NoTriangle 14 newFamily := by
  intro h
  have hp : ∀ A ∈ newFamily, ∀ p ∈ A, p.Prime := by decide +kernel
  have hh := patternCount_le_two_of_noTriangle 14 newFamily hp h
    (fun p => if p = 7 then 6 else 0)
  have ht := new_has_three
  omega

/-- The coordinatewise increasing prime replacement is explicit. -/
def oldPrimes : Fin 3 → ℕ := ![3, 7, 11]
def newPrimes : Fin 3 → ℕ := ![3, 7, 13]

lemma prime_replacement : ∀ i : Fin 3,
    (oldPrimes i).Prime ∧ (newPrimes i).Prime ∧ oldPrimes i ≤ newPrimes i := by
  decide +kernel

#print axioms old_card_le_two
#print axioms new_has_three
#print axioms new_not_no_triangle
end Erdos970.PatternPacking.TriangleTransferObstruction
