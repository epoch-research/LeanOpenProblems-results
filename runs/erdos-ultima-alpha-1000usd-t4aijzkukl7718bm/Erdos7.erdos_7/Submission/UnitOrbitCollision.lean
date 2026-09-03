import FormalConjecturesUtil

/-! A normalized, divisor-closed, irredundant partial congruence family can
induce a cover on an odd-order unit orbit with repeated reduced moduli.
This is not a covering system of the integers: the integer 2 is uncovered. -/

namespace Erdos7UnitOrbitCollision
open Fin.NatCast

abbrev modulus : Fin 5 → ℕ := ![3, 7, 9, 21, 63]
abbrev residue : Fin 5 → ℤ := ![0, 0, 1, 16, 25]
abbrev privatePoint : Fin 5 → ℤ := ![3, 7, 1, 16, 25]

lemma modulus_injective : Function.Injective modulus := by decide +kernel
lemma modulus_odd_nontrivial : ∀ i, Odd (modulus i) ∧ 1 < modulus i := by decide +kernel

lemma divisor_closed : ∀ i, ∀ d ∈ (modulus i).divisors,
    1 < d → ∃ j, modulus j = d := by decide +kernel

lemma private_points : ∀ i,
    (modulus i : ℤ) ∣ privatePoint i - residue i ∧
      ∀ j, j ≠ i → ¬ (modulus j : ℤ) ∣ privatePoint i - residue j := by
  decide +kernel

lemma normalized_primes : ∀ i, (modulus i).Prime → residue i = 0 := by decide +kernel
lemma composite_units : ∀ i, ¬ (modulus i).Prime →
    Nat.Coprime (residue i).natAbs (modulus i) := by decide +kernel
lemma two_uncovered : ∀ i, ¬ (modulus i : ℤ) ∣ 2 - residue i := by decide +kernel

/-- The powers of 58 modulo 63, which has order exactly 3. -/
abbrev orbit : Fin 3 → ℕ := ![1, 58, 25]

lemma orbit_unit : ∀ t, Nat.Coprime (orbit t) 63 := by decide +kernel
lemma orbit_distinct : Function.Injective orbit := by decide +kernel
lemma orbit_mul : ∀ t u : Fin 3, orbit (t + u) % 63 = (orbit t * orbit u) % 63 := by
  decide +kernel

/-- None of the prime classes meets the unit orbit. -/
lemma primes_miss_orbit : ∀ t : Fin 3, ∀ i : Fin 5, i < 2 →
    ¬ (modulus i : ℤ) ∣ (orbit t : ℤ) - residue i := by decide +kernel

/-- Each composite class hits exactly one of the three parameter residues.
The three original moduli are different, but every induced period is 3. -/
lemma composite_preimage : ∀ k t : Fin 3,
    (modulus (↑k.val + 2 : Fin 5) : ℤ) ∣
      (orbit t : ℤ) - residue (↑k.val + 2 : Fin 5) ↔ t = k := by
  decide +kernel

lemma orbit_covered : ∀ t : Fin 3, ∃ i,
    (modulus i : ℤ) ∣ (orbit t : ℤ) - residue i := by decide +kernel

/-- The orbit has exact order 3, so this finite table really is the
multiplicative parameterization `58^n`, not just three unrelated points. -/
lemma orbit_pow (n : ℕ) : orbit (↑n : Fin 3) % 63 = 58 ^ n % 63 := by
  induction n with
  | zero => norm_num [orbit]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, orbit_mul]
    norm_num only [orbit, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Nat.mul_mod, ih, ← Nat.mul_mod, pow_succ]

lemma induced_classes_are_residues_mod_three (n : ℕ) (k : Fin 3) :
    (modulus (↑k.val + 2 : Fin 5) : ℤ) ∣
      (orbit (↑n : Fin 3) : ℤ) - residue (↑k.val + 2 : Fin 5) ↔
      n % 3 = k.val := by
  rw [composite_preimage, Fin.ext_iff]
  rfl

#print axioms divisor_closed
#print axioms private_points
#print axioms orbit_pow
#print axioms induced_classes_are_residues_mod_three
#print axioms two_uncovered
end Erdos7UnitOrbitCollision
