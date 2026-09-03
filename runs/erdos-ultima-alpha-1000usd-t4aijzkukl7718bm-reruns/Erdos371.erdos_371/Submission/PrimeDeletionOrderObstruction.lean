import FormalConjecturesUtil

/-! A finite obstruction to deriving a nonpositive cumulative deletion sum
from max-of-prime-label structure alone. The labels here are NOT the primes'
numerical order. This is not a counterexample to Erdős 371. -/

namespace Erdos371PrimeDeletionOrderObstruction

/-- An injective relabelling, with a deliberately nonnumerical order on the
prime factors that occur in the finite example. -/
def label (p : ℕ) : ℕ :=
  if p = 2 then 8 else
  if p = 19 then 7 else
  if p = 11 then 6 else
  if p = 7 then 5 else
  if p = 13 then 4 else
  if p = 5 then 3 else
  if p = 3 then 2 else
  if p = 17 then 1 else p + 9

set_option maxHeartbeats 4000000 in
lemma label_injective : Function.Injective label := by
  intro a b h
  unfold label at h
  split_ifs at h <;> omega

/-- Maximum of the labels of the prime divisors, with value zero at 0 and 1. -/
def height (n : ℕ) : ℕ := n.primeFactors.sup label

lemma height_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    height (a * b) = max (height a) (height b) := by
  simp [height, Nat.primeFactors_mul ha hb, Finset.sup_union]

def rightSum (N : ℕ) : ℤ :=
  ∑ p ∈ N.primesBelow, ∑ a ∈ Finset.Icc 1 (N / p),
    if height (a * p - 1) < height a then 1 else -1

lemma rightSum_twenty : rightSum 20 = 2 := by
  decide +kernel

/-- The unweighted nonpositivity claim is false for this relabelled maximum.
In particular, the order of the actual primes cannot simply be discarded. -/
theorem not_all_rightSum_nonpositive : ¬ ∀ N, rightSum N ≤ 0 := by
  intro h
  have hh := h 20
  rw [rightSum_twenty] at hh
  omega

/-- The same obstruction already occurs in one fixed-prime prefix. -/
lemma two_prefix_ten :
    (∑ a ∈ Finset.Icc 1 10,
      if height (a*2-1) < height a then (1 : ℤ) else -1) = 6 := by
  decide +kernel

/-- Max-of-prime-label structure alone also does not imply the proposed
fixed-prime prefix inequality. The order here is not the numerical prime order. -/
theorem not_all_fixed_prime_prefix_nonpositive :
    ¬ ∀ p : ℕ, p.Prime → ∀ A : ℕ,
      (∑ a ∈ Finset.Icc 1 A,
        if height (a*p-1) < height a then (1 : ℤ) else -1) ≤ 0 := by
  intro h
  have hh := h 2 (by decide) 10
  rw [two_prefix_ten] at hh
  omega

end Erdos371PrimeDeletionOrderObstruction

#print axioms Erdos371PrimeDeletionOrderObstruction.label_injective
#print axioms Erdos371PrimeDeletionOrderObstruction.not_all_rightSum_nonpositive

#print axioms Erdos371PrimeDeletionOrderObstruction.height_mul

#print axioms Erdos371PrimeDeletionOrderObstruction.not_all_fixed_prime_prefix_nonpositive
