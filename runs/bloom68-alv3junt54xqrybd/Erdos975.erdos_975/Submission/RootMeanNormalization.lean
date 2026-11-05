import Submission.RootMeanBasic
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# Monic normalization of integer polynomial root counts

For a nonconstant irreducible integer polynomial `f`, Mathlib's
`f.integralNormalization` is a monic irreducible integer polynomial of the
same natural degree. Writing `a = f.leadingCoeff` and `d = f.natDegree`, it is
`X ^ d + ∑ i < d, C (f.coeff i * a ^ (d - 1 - i)) * X ^ i` and satisfies
`g(a * x) = a ^ (d - 1) * f(x)` in every commutative residue ring.

Multiplication by `a` therefore bijects the root sets modulo every modulus
coprime to `a.natAbs`. In particular, the root counts agree at every prime
not dividing `a`. The final existence theorems give the positive exceptional
modulus `a.natAbs`; no root-count mean is assumed in this file.
-/

namespace Erdos975Support

open Polynomial

/-- Scaling roots by a unit is a multiplicative equivalence. It need not be
additive: its definition depends on the degree of the polynomial. -/
private noncomputable def scaleRootsMulEquiv {R : Type*} [CommSemiring R]
    [NoZeroDivisors R] (u : Rˣ) : R[X] ≃* R[X] where
  toFun p := p.scaleRoots (u : R)
  invFun p := p.scaleRoots (↑(u⁻¹) : R)
  left_inv p := by simp [← scaleRoots_mul]
  right_inv p := by simp [← scaleRoots_mul]
  map_mul' p q := mul_scaleRoots_of_noZeroDivisors p q (u : R)

/-- The integral normalization of a nonconstant irreducible integer polynomial
is irreducible over the integers. The proof uses Gauss's lemma and the
multiplicative equivalence `scaleRoots` over `ℚ`. -/
theorem integralNormalization_irreducible (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : 0 < f.natDegree) : Irreducible f.integralNormalization := by
  have hF : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (hf.isPrimitive (Nat.ne_of_gt hdeg))).mp hf
  let F := f.map (Int.castRingHom ℚ)
  have ha : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF.ne_zero
  have hs : Irreducible (F.scaleRoots F.leadingCoeff) :=
    (MulEquiv.irreducible_iff (scaleRootsMulEquiv (Units.mk0 _ ha))).mpr hF
  have hi : Irreducible F.integralNormalization := by
    have hu : IsUnit (C F.leadingCoeff) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
    apply (irreducible_mul_isUnit hu).mp
    rwa [integralNormalization_mul_C_leadingCoeff]
  have haZ : (Int.castRingHom ℚ) f.leadingCoeff ≠ 0 := by
    rw [Int.coe_castRingHom]
    change (f.leadingCoeff : ℚ) ≠ 0
    exact_mod_cast (leadingCoeff_ne_zero.mpr hf.ne_zero)
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (monic_integralNormalization hf.ne_zero).isPrimitive).mpr
  rw [← integralNormalization_map (Int.castRingHom ℚ) f haZ]
  exact hi

/-- Multiplication by the leading coefficient identifies residue roots of `f`
with residue roots of its integral normalization whenever that coefficient is
invertible. This also works over composite moduli, without a domain hypothesis. -/
noncomputable def polynomialRootsIntegralNormalizationEquiv (f : ℤ[X])
    (hdeg : 0 < f.natDegree) (q : ℕ)
    (hu : IsUnit (f.leadingCoeff : ZMod q)) :
    {x : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) x = 0} ≃
      {x : ZMod q // f.integralNormalization.eval₂ (Int.castRingHom (ZMod q)) x = 0} := by
  refine Equiv.subtypeEquiv hu.unit.mulLeft ?_
  intro x
  change f.eval₂ (Int.castRingHom (ZMod q)) x = 0 ↔
    f.integralNormalization.eval₂ (Int.castRingHom (ZMod q))
      ((hu.unit : ZMod q) * x) = 0
  have heval := integralNormalization_eval₂_leadingCoeff_mul hdeg
    (Int.castRingHom (ZMod q)) x
  simp only [Int.coe_castRingHom] at heval
  rw [hu.unit_spec, heval]
  exact (IsUnit.mul_right_eq_zero (hu.pow (f.natDegree - 1))).symm

/-- Root counts are unchanged by integral normalization whenever the leading
coefficient is invertible modulo `q`. The zero-modulus convention is included. -/
theorem rootCount_integralNormalization_of_isUnit (f : ℤ[X])
    (hdeg : 0 < f.natDegree) (q : ℕ)
    (hu : IsUnit (f.leadingCoeff : ZMod q)) :
    rootCount (polynomialAbsValue f) q =
      rootCount (polynomialAbsValue f.integralNormalization) q := by
  by_cases hq : q = 0
  · simp [hq]
  letI : NeZero q := ⟨hq⟩
  rw [rootCount_polynomial_eq_card_zmod, rootCount_polynomial_eq_card_zmod]
  exact Nat.card_congr (polynomialRootsIntegralNormalizationEquiv f hdeg q hu)

/-- The comparison holds at every modulus coprime to the absolute leading
coefficient, not merely at good primes. -/
theorem rootCount_integralNormalization_of_coprime (f : ℤ[X])
    (hdeg : 0 < f.natDegree) (q : ℕ) (hq : q.Coprime f.leadingCoeff.natAbs) :
    rootCount (polynomialAbsValue f) q =
      rootCount (polynomialAbsValue f.integralNormalization) q := by
  apply rootCount_integralNormalization_of_isUnit f hdeg q
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime,
    Int.natAbs_natCast]
  exact hq

/-- At every prime not dividing the leading coefficient, `f` and its monic
integral normalization have exactly the same root count. -/
theorem rootCount_integralNormalization_prime (f : ℤ[X])
    (hdeg : 0 < f.natDegree) (p : ℕ) (hp : p.Prime)
    (hpa : ¬ (p : ℤ) ∣ f.leadingCoeff) :
    rootCount (polynomialAbsValue f) p =
      rootCount (polynomialAbsValue f.integralNormalization) p := by
  letI : Fact p.Prime := ⟨hp⟩
  apply rootCount_integralNormalization_of_isUnit f hdeg p
  apply isUnit_iff_ne_zero.mpr
  exact mt (ZMod.intCast_zmod_eq_zero_iff_dvd f.leadingCoeff p).mp hpa

/-- An explicit monic irreducible normalization with all good-modulus root
counts preserved and the original degree unchanged. -/
theorem exists_monic_irreducible_rootCount_eq_of_coprime (f : ℤ[X])
    (hf : Irreducible f) (hdeg : 0 < f.natDegree) :
    ∃ g : ℤ[X], g.Monic ∧ Irreducible g ∧ g.natDegree = f.natDegree ∧
      ∀ q : ℕ, q.Coprime f.leadingCoeff.natAbs →
        rootCount (polynomialAbsValue f) q = rootCount (polynomialAbsValue g) q := by
  refine ⟨f.integralNormalization, monic_integralNormalization hf.ne_zero,
    integralNormalization_irreducible f hf hdeg, natDegree_integralNormalization, ?_⟩
  intro q hq
  exact rootCount_integralNormalization_of_coprime f hdeg q hq

/-- There is a monic irreducible normalization and a genuinely positive finite
bad modulus. The witnesses are `f.integralNormalization` and
`f.leadingCoeff.natAbs`, and equality holds outside its prime divisors. -/
theorem exists_monic_irreducible_rootCount_eq_good_primes (f : ℤ[X])
    (hf : Irreducible f) (hdeg : 0 < f.natDegree) :
    ∃ (g : ℤ[X]) (D : ℕ), g.Monic ∧ Irreducible g ∧
      g.natDegree = f.natDegree ∧ 0 < D ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ D →
        rootCount (polynomialAbsValue f) p = rootCount (polynomialAbsValue g) p := by
  refine ⟨f.integralNormalization, f.leadingCoeff.natAbs,
    monic_integralNormalization hf.ne_zero, integralNormalization_irreducible f hf hdeg,
    natDegree_integralNormalization,
    Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero), ?_⟩
  intro p hp hpD
  apply rootCount_integralNormalization_prime f hdeg p hp
  rwa [Int.natCast_dvd]

end Erdos975Support
