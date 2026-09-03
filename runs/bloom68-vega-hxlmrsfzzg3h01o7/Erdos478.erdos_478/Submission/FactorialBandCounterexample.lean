import Submission.FactorialBand

/-!
# A counterexample to full omission of seven in the five-band progression

The prime `6701` satisfies `6701 % 6699 = 2`, but
`52! * 6626! = 7` in `ZMod 6701`. The sum `52 + 6626 = 6678` is outside
`{6701-3, 6701-2, 6701-1, 6701, 6701+1}`, so this is consistent with
`FactorialBand.factorial_mul_ne_seven_in_five_bands`.

Only the small factorials `52!` and `74!` are evaluated. The large factorial
`6626!` is handled symbolically by `FactorialPairing.factorial_mul_reflection`
at `k = 74`. All numerical proofs use kernel-checked tactics.

This refutes the assertion that seven is fully omitted for every prime in
this progression; it does not refute five-band avoidance. It does not decide
whether some other nonzero residue is omitted at `6701`, whether there are
infinitely many missing-product primes, or the factorial-residue asymptotic
in Erdős problem 478. No specification file is imported or changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace FactorialBandCounterexample

/-- The concrete modulus is prime. -/
theorem prime_6701 : Nat.Prime 6701 := by
  norm_num

/-- The modulus lies in the progression used by the five-band theorem. -/
theorem progression_6701 : 6701 % 6699 = 2 := by
  norm_num

/-- The first small factorial residue. -/
theorem factorial_52_mod : Nat.factorial 52 % 6701 = 3195 := by
  norm_num

/-- The small factorial residue needed for Wilson reflection. -/
theorem factorial_74_mod : Nat.factorial 74 % 6701 = 4330 := by
  norm_num

theorem factorial_52_cast : (Nat.factorial 52 : ZMod 6701) = 3195 := by
  rw [← ZMod.natCast_mod (Nat.factorial 52) 6701, factorial_52_mod]
  norm_num

theorem factorial_74_cast : (Nat.factorial 74 : ZMod 6701) = 4330 := by
  rw [← ZMod.natCast_mod (Nat.factorial 74) 6701, factorial_74_mod]
  norm_num

/-- The two small factorials differ by the multiplier `-7`. -/
theorem factorial_52_eq_neg_seven_mul_74 :
    (Nat.factorial 52 : ZMod 6701) = -7 * (Nat.factorial 74 : ZMod 6701) := by
  rw [factorial_52_cast, factorial_74_cast]
  decide

/-- Wilson reflection, without evaluating `6626!`. -/
theorem factorial_74_mul_6626 :
    (Nat.factorial 74 : ZMod 6701) * (Nat.factorial 6626 : ZMod 6701) = -1 := by
  letI : Fact (Nat.Prime 6701) := ⟨prime_6701⟩
  have h := FactorialPairing.factorial_mul_reflection
    (p := 6701) (k := 74) (by decide)
  have hsign : (-1 : ZMod 6701) ^ (74 + 1) = -1 := by norm_num
  simpa only [show 6701 - 1 - 74 = 6626 by decide, hsign] using h

/-- The explicit product equal to seven; the large factorial stays symbolic. -/
theorem factorial_product_eq_seven :
    (Nat.factorial 52 : ZMod 6701) * (Nat.factorial 6626 : ZMod 6701) = 7 := by
  rw [factorial_52_eq_neg_seven_mul_74, mul_assoc, factorial_74_mul_6626]
  norm_num

/-- The same product equality, as a remainder of a natural-number product. -/
theorem factorial_product_mod :
    (Nat.factorial 52 * Nat.factorial 6626) % 6701 = 7 := by
  have h := congrArg ZMod.val factorial_product_eq_seven
  rw [← Nat.cast_mul, ZMod.val_natCast] at h
  exact h

theorem index_sum : (52 + 6626 : ℕ) = 6678 := by
  norm_num

/-- The example is not in any of the five bands covered by `FactorialBand`. -/
theorem sum_outside_five_bands :
    52 + 6626 ∉ ({6701 - 3, 6701 - 2, 6701 - 1, 6701, 6701 + 1} : Finset ℕ) := by
  norm_num

/-- All arithmetic, index-range, product, and band conditions in one statement. -/
theorem counterexample_6701 :
    Nat.Prime 6701 ∧ 29 < (6701 : ℕ) ∧ 6701 % 6699 = 2 ∧
      1 ≤ (52 : ℕ) ∧ 52 < 6701 ∧ 1 ≤ (6626 : ℕ) ∧ 6626 < 6701 ∧
      (Nat.factorial 52 : ZMod 6701) * (Nat.factorial 6626 : ZMod 6701) = 7 ∧
      52 + 6626 ∉ ({6701 - 3, 6701 - 2, 6701 - 1, 6701, 6701 + 1} : Finset ℕ) := by
  exact ⟨prime_6701, by decide, progression_6701,
    by decide, by decide, by decide, by decide,
    factorial_product_eq_seven, sum_outside_five_bands⟩

section

open scoped Pointwise

-- Keep the concrete residue set symbolic rather than enumerating all its factorials.
attribute [local irreducible] FactorialPairing.residues

/-- Seven belongs to the full product of the factorial-residue set with itself. -/
theorem seven_mem_residue_product :
    (7 : ZMod 6701) ∈ FactorialPairing.residues 6701 * FactorialPairing.residues 6701 := by
  letI : Fact (Nat.Prime 6701) := ⟨prime_6701⟩
  have h := Finset.mul_mem_mul
    (FactorialPairing.factorial_mem_residues (p := 6701) (k := 52) (by decide))
    (FactorialPairing.factorial_mem_residues (p := 6701) (k := 6626) (by decide))
  rw [factorial_product_eq_seven] at h
  exact h

end

/-- Dropping the band hypothesis from the progression-wide avoidance claim is false. -/
theorem not_full_seven_omission :
    ¬ (∀ p : ℕ, p.Prime → 29 < p → p % 6699 = 2 →
      ∀ i j : ℕ, i < p → j < p →
        (i.factorial : ZMod p) * (j.factorial : ZMod p) ≠ 7) := by
  intro h
  exact h 6701 prime_6701 (by decide) progression_6701 52 6626
    (by decide) (by decide) factorial_product_eq_seven

end FactorialBandCounterexample

#print axioms FactorialBandCounterexample.prime_6701
#print axioms FactorialBandCounterexample.progression_6701
#print axioms FactorialBandCounterexample.factorial_52_mod
#print axioms FactorialBandCounterexample.factorial_74_mod
#print axioms FactorialBandCounterexample.factorial_52_cast
#print axioms FactorialBandCounterexample.factorial_74_cast
#print axioms FactorialBandCounterexample.factorial_52_eq_neg_seven_mul_74
#print axioms FactorialBandCounterexample.factorial_74_mul_6626
#print axioms FactorialBandCounterexample.factorial_product_eq_seven
#print axioms FactorialBandCounterexample.factorial_product_mod
#print axioms FactorialBandCounterexample.index_sum
#print axioms FactorialBandCounterexample.sum_outside_five_bands
#print axioms FactorialBandCounterexample.counterexample_6701
#print axioms FactorialBandCounterexample.seven_mem_residue_product
#print axioms FactorialBandCounterexample.not_full_seven_omission
