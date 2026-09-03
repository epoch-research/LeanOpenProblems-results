import Submission.SignatureGridCores

/-! Arithmetic realization of the partial grid family. This is not a covering
 system: an uncovered integer is part of the verified conclusion. -/
namespace Erdos7SignatureGridArithmetic
open scoped BigOperators
open Finset Erdos7SignatureGridPatterns Erdos7SignatureGridFamily
set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable def m (d : Pattern) : ℕ :=
  Erdos7PrimePowerBoxRealization.modulus prime (exponent d)

lemma prime_prime (i : Coord) : (prime i).Prime := (prime_properties.2 i).1

lemma modulus_injective : Function.Injective m := by
  intro d k h
  apply exponent_injective
  exact Erdos7PrimePowerBoxRealization.modulus_injective prime prime_prime prime_properties.1 h

lemma modulus_odd (d : Pattern) : Odd (m d) := by
  change Odd (∏ i, prime i ^ exponent d i)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  exact ((prime_properties.2 0).2.1.pow).mul
    (((prime_properties.2 1).2.1.pow).mul ((prime_properties.2 2).2.1.pow))

lemma modulus_nontrivial (d : Pattern) : 1 < m d := by
  have hp : 0 < m d := Erdos7PrimePowerBoxRealization.modulus_pos prime prime_prime _
  have hn : m d ≠ 1 := by
    intro h
    obtain ⟨i, hi⟩ := exponent_nonzero d
    apply hi
    have hf := Erdos7PrimePowerBoxRealization.factorization_at prime prime_prime
      prime_properties.1 (exponent d) i
    change (m d).factorization (prime i) = exponent d i at hf
    rw [h] at hf
    simpa using hf.symm
  omega

/-- Every nontrivial divisor is already represented. -/
theorem divisor_closed (d : Pattern) (n : ℕ) (hn : 1 < n) (hd : n ∣ m d) :
    ∃ k : Pattern, m k = n := by
  obtain ⟨f, hf, hm⟩ := Erdos7PrimePowerBoxRealization.divisor_pattern prime prime_prime
    prime_properties.1 (exponent d) n hd
  have hb : ∑ i, f i ≤ 82 :=
    (sum_le_sum (fun i _ => hf i)).trans (exponentRaw_sum d.val)
  have hf0 : ∃ i, f i ≠ 0 := by
    by_contra! hh
    have hz : f = fun _ => 0 := funext hh
    rw [hz] at hm
    simp [Erdos7PrimePowerBoxRealization.modulus] at hm
    omega
  obtain ⟨k, hk⟩ := exists_pattern_of_bound f hb hf0
  refine ⟨k, ?_⟩
  dsimp [m]
  rw [hk]
  exact hm

/-- Integer residues, private integers, and an uncovered integer, all for the
 SAME divisor-closed odd family with distinct nontrivial moduli. -/
theorem arithmetic_partial_family : ∃ (a z : Pattern → ℤ) (v : ℤ),
    (∀ d i, (prime i : ℤ) ^ 82 ∣ a d - residue d i) ∧
    (∀ d k, ((m k : ℤ) ∣ z d - a k) ↔ k = d) ∧
    ∀ k, ¬ (m k : ℤ) ∣ v - a k := by
  exact Erdos7PrimePowerBoxRealization.realize_partial_family prime prime_prime
    prime_properties.1 (fun _ => 82) exponent exponent_bound residue residue (fun _ => -1)
    private_residue stem_not_hit

/-- CRT transfers the local box membership for every integer realizing the
 chosen coordinate tuple, not only the private-point witnesses. -/
lemma membership_transfer (a : Pattern → ℤ)
    (ha : ∀ d i, (prime i : ℤ) ^ 82 ∣ a d - residue d i)
    (x : Coord → ℤ) (z : ℤ) (hz : ∀ i, (prime i : ℤ) ^ 82 ∣ z - x i) (d : Pattern) :
    ((m d : ℤ) ∣ z - a d) ↔ Hits x d := by
  exact Erdos7PrimePowerBoxRealization.realized_membership prime prime_prime prime_properties.1
    (fun _ => 82) (exponent d) (exponent_bound d) x (residue d) z (a d) hz (ha d)

#print axioms modulus_injective
#print axioms modulus_odd
#print axioms modulus_nontrivial
#print axioms divisor_closed
#print axioms arithmetic_partial_family
#print axioms membership_transfer
end Erdos7SignatureGridArithmetic
