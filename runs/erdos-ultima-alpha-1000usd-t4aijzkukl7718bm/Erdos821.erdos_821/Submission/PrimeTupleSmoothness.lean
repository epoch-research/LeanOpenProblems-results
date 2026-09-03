import Submission.Work

/-!
# Size requirements for prime-input successor tuples

A root-smooth predecessor `a*q` with prime input `q` forces a large
multiplier `a`. In particular, fixed finite multiplier families cannot
supply infinitely many such successors at any root order at least two.
These are restrictions on a proposed construction, not a disproof of
Erdős 821 and not a claim about the frequency of prime tuples.
-/

open Nat Finset
open scoped Classical

namespace Erdos821

lemma root_smooth_prime_input_multiplier_bound (a q k : ℕ) (hq : q.Prime)
    (hk : 1 ≤ k) (hs : a*q ∈ smoothShiftedPredecessors k) :
    q^(k-1) ≤ a := by
  have haq : 0 < a*q := by
    have h := hs.1.two_le
    omega
  have hqmem : q ∈ (a*q).primeFactors :=
    hq.mem_primeFactors (Nat.dvd_mul_left q a) haq.ne'
  have hpow := hs.2 q hqmem
  have he : q^(k-1)*q = q^k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  exact Nat.le_of_mul_le_mul_right (by simpa only [he] using hpow) hq.pos

lemma root_smooth_prime_input_le_multiplier (a q k : ℕ) (hq : q.Prime)
    (hk : 2 ≤ k) (hs : a*q ∈ smoothShiftedPredecessors k) : q ≤ a := by
  have hpow : q ≤ q^(k-1) := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right hq.pos (show 1 ≤ k-1 by omega))
  exact hpow.trans (root_smooth_prime_input_multiplier_bound a q k hq (by omega) hs)

lemma root_smooth_prime_input_successor_bound (a q k : ℕ) (hq : q.Prime)
    (hk : 2 ≤ k) (hs : a*q ∈ smoothShiftedPredecessors k) :
    a*q+1 ≤ a^2+1 := by
  have hq := root_smooth_prime_input_le_multiplier a q k hq hk hs
  simpa only [sq] using Nat.add_le_add_right (Nat.mul_le_mul_left a hq) 1

/-- This set is finite regardless of whether the corresponding prime
linear forms take prime values infinitely often without smoothness. -/
theorem finite_root_smooth_prime_input_successors (A : Finset ℕ) (k : ℕ)
    (hk : 2 ≤ k) :
    {p : ℕ | ∃ a ∈ A, ∃ q : ℕ, q.Prime ∧ p=a*q+1 ∧
      p-1 ∈ smoothShiftedPredecessors k}.Finite := by
  apply (Set.finite_Iic ((A.sup id)^2+1)).subset
  rintro p ⟨a,ha,q,hq,rfl,hs⟩
  simp only [Nat.add_sub_cancel] at hs
  have hbound := root_smooth_prime_input_successor_bound a q k hq hk hs
  have haA : a ≤ A.sup id := Finset.le_sup (f := id) ha
  exact hbound.trans (Nat.add_le_add_right (Nat.pow_le_pow_left haA 2) 1)

/-- A polynomially growing multiplier still imposes an upper bound on
which root orders can occur. The exponent bound on the multiplier is an
explicit assumption, not an estimate for a sieve construction. -/
theorem root_smooth_prime_input_order_bound (a q j k : ℕ) (hq : q.Prime)
    (ha : a ≤ q^j) (hs : a*q ∈ smoothShiftedPredecessors k) : k ≤ j+1 := by
  by_contra h
  have hk : 1 ≤ k := by omega
  have hle := (root_smooth_prime_input_multiplier_bound a q k hq hk hs).trans ha
  have hlt : q^j < q^(k-1) :=
    Nat.pow_lt_pow_right hq.one_lt (by omega)
  exact hlt.not_ge hle

/-- If the retained prime input lies above a sieve cutoff Q, a k-th-root
smooth successor is larger than Q^k. Thus an estimate whose unit-support
condition is supplied by Q <= q cannot have near-full ambient level here. -/
lemma root_smooth_successor_above_cutoff_power (a q k Q : ℕ) (hq : q.Prime)
    (hQ : Q ≤ q) (hs : a*q ∈ smoothShiftedPredecessors k) :
    Q^k < a*q+1 := by
  have haq : 0 < a*q := by have h := hs.1.two_le; omega
  have hqmem : q ∈ (a*q).primeFactors :=
    hq.mem_primeFactors (Nat.dvd_mul_left q a) haq.ne'
  exact (Nat.pow_le_pow_left hQ k).trans_lt ((hs.2 q hqmem).trans_lt (Nat.lt_succ_self _))

end Erdos821
