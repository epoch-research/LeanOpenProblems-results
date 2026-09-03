import FormalConjecturesUtil

/-! A finite check of a proposed auxiliary pairing, not a disproof of Erdős 371. -/
namespace Erdos371

def reflectedInBlock (Q n : ℕ) : ℕ := Q*(n/Q)+(Q-1-n%Q)

/-- The reflection within the block of length 2*3 sends 8 to 9.
Both adjacent comparisons rise: the reflected pair acquires the larger
prime 5, so swapping the chosen divisors does not reverse the sign. -/
theorem reflectedInBlock_does_not_reverse_comparison :
    reflectedInBlock 6 8 = 9 ∧
    Nat.maxPrimeFac 8 < Nat.maxPrimeFac 9 ∧
    Nat.maxPrimeFac 9 < Nat.maxPrimeFac 10 := by
  decide +kernel

#print axioms reflectedInBlock_does_not_reverse_comparison
end Erdos371
