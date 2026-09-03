import Submission.ContinuousIntervalReference

/-! Kernel-checked uniform finite bounds from the transferred interval envelope.
These are finite examples, not a proof of uniform quadratic growth. -/
namespace Erdos970.ContinuousInterval

def firstHundredPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541]

def firstHundredMarginal (i : ℕ) : ℚ := 1 / (firstHundredPrimes.getD i 1 : ℚ)

theorem firstHundred_nth (i : Fin 100) :
    firstHundredPrimes.getD i.val 1 = Nat.nth Nat.Prime i.val := by
  have h : ∀ i : Fin 100, (firstHundredPrimes.getD i.val 1).Prime ∧
      Nat.count Nat.Prime (firstHundredPrimes.getD i.val 1) = i.val := by
    decide +kernel
  have hh := Nat.nth_count (h i).1
  rw [(h i).2] at hh
  exact hh.symm

theorem referencePositive_of_firstHundred (k m : ℕ) (hk : k ≤ 100)
    (hpos : 0 < (fastEnvelope firstHundredMarginal k (m : ℚ)).1) : ReferencePositive k m := by
  have he := fastEnvelope_congr firstHundredMarginal referenceMarginal k
    (fun i hi => by
      simp only [firstHundredMarginal, referenceMarginal,
        firstHundred_nth ⟨i, hi.trans_le hk⟩]) (m : ℚ)
  unfold ReferencePositive
  rwa [← he]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem firstFifty_fast_positive :
    0 < (fastEnvelope firstHundredMarginal 50 (5000 : ℚ)).1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem firstHundred_fast_positive :
    0 < (fastEnvelope firstHundredMarginal 100 (25000 : ℚ)).1 := by
  decide +kernel

theorem jacobsthalFunction_fifty_le_five_thousand : jacobsthalFunction 50 ≤ 5000 :=
  jacobsthalFunction_le_of_referencePositive 50 5000
    (referencePositive_of_firstHundred 50 5000 (by omega) firstFifty_fast_positive)

theorem jacobsthalFunction_hundred_le_twenty_five_thousand : jacobsthalFunction 100 ≤ 25000 :=
  jacobsthalFunction_le_of_referencePositive 100 25000
    (referencePositive_of_firstHundred 100 25000 le_rfl firstHundred_fast_positive)

#print axioms jacobsthalFunction_fifty_le_five_thousand
#print axioms jacobsthalFunction_hundred_le_twenty_five_thousand
end Erdos970.ContinuousInterval
