import Submission.RecursiveReferenceCriterion

/-! A finite kernel-checked instance of the recursive sieve. It is not a uniform bound. -/
namespace Erdos970.RecursiveSieve

def firstFiftyPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229]

def firstFiftyMarginal (i : ℕ) : ℚ := 1 / (firstFiftyPrimes.getD i 1 : ℚ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem firstFifty_linear_positive :
    0 < (linearEnvelope firstFiftyMarginal 50 15000).1 := by
  decide +kernel

theorem firstFifty_nth (i : Fin 50) :
    firstFiftyPrimes.getD i.val 1 = Nat.nth Nat.Prime i.val := by
  have h : ∀ i : Fin 50, (firstFiftyPrimes.getD i.val 1).Prime ∧
      Nat.count Nat.Prime (firstFiftyPrimes.getD i.val 1) = i.val := by
    decide +kernel
  have hh := Nat.nth_count (h i).1
  rw [(h i).2] at hh
  exact hh.symm

theorem referencePositive_fifty : ReferencePositive 50 15000 := by
  have he := linearEnvelope_congr firstFiftyMarginal
    (fun i => 1 / (Nat.nth Nat.Prime i : ℚ)) 50 (15000 : ℚ)
    (fun i hi => by simp only [firstFiftyMarginal, firstFifty_nth ⟨i,hi⟩])
  unfold ReferencePositive
  norm_num only [Nat.cast_ofNat]
  rw [← he]
  exact firstFifty_linear_positive

theorem isJacobsthalBound_fifty : IsJacobsthalBound 50 15000 :=
  isJacobsthalBound_of_referencePositive 50 15000 referencePositive_fifty

theorem jacobsthalFunction_fifty_le : jacobsthalFunction 50 ≤ 15000 :=
  (jacobsthalFunction_le_iff 50 15000).mpr isJacobsthalBound_fifty

#print axioms jacobsthalFunction_fifty_le
#print axioms firstFifty_linear_positive
end Erdos970.RecursiveSieve
