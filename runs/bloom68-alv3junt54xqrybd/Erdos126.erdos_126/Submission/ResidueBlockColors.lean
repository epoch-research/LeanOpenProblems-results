import Submission.ResidueBlockCounts

/-!
# Prime-color opposition at every nonself sum level

A nonself sum level lies strictly above the height of a doubled summand.
The two summands must therefore have equal prime heights.  Stripping their
common prime-power factor leaves opposite nonzero digits at an odd prime,
and opposite odd residues modulo four at the prime two.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos126Aux.ResidueBlocks

/-- The global digit color flips across every nonself opposite residue pair. -/
theorem primeColor_ne_of_nonself_add {p k x y : ℕ} (hp : p.Prime)
    (hx : 0 < x) (hy : 0 < y)
    (hsum : p ^ k ∣ x + y) (hself : ¬p ^ k ∣ 2 * x) :
    primeColor p x ≠ primeColor p y := by
  have hk : k ≤ (x + y).factorization p :=
    (hp.pow_dvd_iff_le_factorization (by omega : x + y ≠ 0)).1 hsum
  have hdouble : (2 * x).factorization p < k := by
    by_contra h
    exact hself ((hp.pow_dvd_iff_le_factorization (by omega : 2 * x ≠ 0)).2 (by omega))
  have hheight : x.factorization p < k := by
    rw [factorization_two_mul hx] at hdouble
    omega
  have heq : x.factorization p = y.factorization p := by
    by_contra h
    rw [factorization_add_eq_min_of_ne hp hx hy h] at hk
    have hm := min_le_left (x.factorization p) (y.factorization p)
    omega
  have he : x + y = p ^ x.factorization p * (primeUnitPart p x + primeUnitPart p y) := by
    calc
      x + y = p ^ x.factorization p * primeUnitPart p x +
          p ^ y.factorization p * primeUnitPart p y := by
        simp only [primeUnitPart, Nat.ordProj_mul_ordCompl_eq_self]
      _ = _ := by rw [← heq, mul_add]
  have hunit (d : ℕ) (hd : x.factorization p + d ≤ k) :
      p ^ d ∣ primeUnitPart p x + primeUnitPart p y := by
    have hv : p ^ (x.factorization p + d) ∣ x + y := (pow_dvd_pow p hd).trans hsum
    rw [he, pow_add] at hv
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp.pos) hv
  by_cases hp2 : p = 2
  · subst p
    have hd : x.factorization 2 + 2 ≤ k := by
      rw [factorization_two_mul hx] at hdouble
      simp only [if_true] at hdouble
      omega
    have hfour : 4 ∣ primeUnitPart 2 x + primeUnitPart 2 y := by
      simpa only [Nat.reducePow] using hunit 2 hd
    exact primeColor_two_ne hx hfour
  · have hpdvd : p ∣ primeUnitPart p x + primeUnitPart p y := by
      simpa only [pow_one] using hunit 1 (by omega)
    exact primeColor_ne_of_odd_prime hp hp2 hx hpdvd

variable {ι : Type*} [Fintype ι]

/-- Unconditional entrywise cross-kernel identity for the finite residue
blocks, at any cutoff covering all sum valuations in the chosen primes. -/
theorem crossSum_eq_primeExcessKernel (a : ι → ℕ) (S : Finset ℕ) (M : ℕ)
    (ha : ∀ i, 0 < a i) (hS : ∀ p ∈ S, p.Prime)
    (hM : ∀ p ∈ S, ∀ i j, (a i + a j).factorization p ≤ M) (i j : ι) :
    Paired.crossSum (nodeBlock a S M) i j = primeExcessKernel a S i j := by
  apply crossSum_eq_primeExcess_of_color_opposition a S M ha hS hM
  intro p hp k i j hsum hself
  exact primeColor_ne_of_nonself_add (hS p hp) (ha i) (ha j) hsum hself

end Erdos126Aux.ResidueBlocks
