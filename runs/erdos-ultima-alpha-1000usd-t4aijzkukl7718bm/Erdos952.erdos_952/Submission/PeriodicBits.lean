import Submission.BitsetBarrier

/-! Periodic low-bit masks, with algebraic correctness independent of their construction. -/

namespace Erdos952Investigation.BitsetBarrier

set_option maxHeartbeats 0

lemma periodic_bits {M p s b : ℕ} (hp : 0 < p)
    (hlow : s % (1 <<< p) = b)
    (hshift : s >>> p = s % (1 <<< (M - p))) :
    ∀ i, i < M → s.testBit i = b.testBit (i % p) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hip : i < p
    · have he := congrArg (fun n : ℕ => n.testBit i) hlow
      simpa [Nat.shiftLeft_eq, Nat.testBit_mod_two_pow, hip, Nat.mod_eq_of_lt hip] using he
    · have hpi : p ≤ i := by omega
      have hj : i - p < M - p := by omega
      have he := congrArg (fun n : ℕ => n.testBit (i - p)) hshift
      have hsum : p + (i - p) = i := by omega
      have he' : s.testBit i = s.testBit (i - p) := by
        simpa [Nat.testBit_shiftRight, Nat.shiftLeft_eq, Nat.testBit_mod_two_pow, hj, hsum] using he
      have hmod : (i - p) % p = i % p := by
        nth_rw 2 [← Nat.sub_add_cancel hpi]
        simp
      exact he'.trans ((ih (i - p) (by omega) (by omega)).trans (congrArg b.testBit hmod))

#print axioms periodic_bits

end Erdos952Investigation.BitsetBarrier
