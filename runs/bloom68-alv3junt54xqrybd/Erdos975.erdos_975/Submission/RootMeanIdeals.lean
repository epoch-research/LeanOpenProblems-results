import Submission.RootMeanBasic

/-!
# Roots and cyclic quotient ideals

For every integer polynomial and every positive modulus, its residue roots
are in bijection with ideals of the order `ℤ[X] / (f)` whose quotient ring is
`ZMod q`. Thus the existing root count really counts cyclic quotient ideals
of this order. This is not a claim that all ideals in the maximal order have
cyclic quotient, nor an identification of the two orders at bad primes.

The quotient-ideal bijection uses no monicity assumption. Primitivity,
monicity, and good-prime Kummer–Dedekind hypotheses enter separately when
passing to a number field's maximal order.
-/

namespace Erdos975Support

open Polynomial

/-- Ideals whose quotient is the cyclic residue ring `ZMod q`. -/
def ZModQuotientIdeals (R : Type*) [CommRing R] (q : ℕ) :=
  {I : Ideal R // Nonempty (R ⧸ I ≃+* ZMod q)}

/-- A ring homomorphism to `ZMod q` is always surjective, since integer
casts exhaust the target. This also holds at `q = 0`. -/
theorem ringHom_zmod_surjective {R : Type*} [Ring R] {q : ℕ} (φ : R →+* ZMod q) :
    Function.Surjective φ := by
  intro x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x
  exact ⟨(z : R), by simpa only [map_intCast] using hz⟩

/-- Maps to a cyclic residue ring are determined by their kernels.
The key point is uniqueness of every ring endomorphism of `ZMod q`. -/
theorem ringHom_zmod_eq_of_ker_eq {R : Type*} [CommRing R] {q : ℕ}
    (φ ψ : R →+* ZMod q) (h : RingHom.ker φ = RingHom.ker ψ) : φ = ψ := by
  let eφ := φ.quotientKerEquivOfSurjective (ringHom_zmod_surjective φ)
  let eψ := ψ.quotientKerEquivOfSurjective (ringHom_zmod_surjective ψ)
  let e : ZMod q ≃+* ZMod q := eφ.symm.trans ((Ideal.quotEquivOfEq h).trans eψ)
  have he : e = RingEquiv.refl (ZMod q) := Subsingleton.elim _ _
  ext r
  have hφ : eφ (Ideal.Quotient.mk (RingHom.ker φ) r) = φ r :=
    RingHom.quotientKerEquivOfSurjective_apply_mk _ _
  have hψ : eψ (Ideal.Quotient.mk (RingHom.ker ψ) r) = ψ r :=
    RingHom.quotientKerEquivOfSurjective_apply_mk _ _
  have hr : e (φ r) = ψ r := by
    change eψ (Ideal.quotEquivOfEq h (eφ.symm (φ r))) = ψ r
    rw [← hφ, eφ.symm_apply_apply, Ideal.quotEquivOfEq_mk, hψ]
  simpa only [he, RingEquiv.refl_apply] using hr

/-- Ring homomorphisms to `ZMod q` correspond exactly to ideals with that
quotient ring. No choice of quotient isomorphism is counted more than once. -/
noncomputable def ringHomsEquivZModQuotientIdeals (R : Type*) [CommRing R] (q : ℕ) :
    (R →+* ZMod q) ≃ ZModQuotientIdeals R q := by
  classical
  apply Equiv.ofBijective
    (fun φ ↦ ⟨RingHom.ker φ,
      ⟨φ.quotientKerEquivOfSurjective (ringHom_zmod_surjective φ)⟩⟩)
  constructor
  · intro φ ψ h
    exact ringHom_zmod_eq_of_ker_eq φ ψ (congrArg Subtype.val h)
  · intro I
    obtain ⟨e⟩ := I.2
    let φ : R →+* ZMod q := e.toRingHom.comp (Ideal.Quotient.mk I.1)
    refine ⟨φ, Subtype.ext ?_⟩
    ext r
    change e (Ideal.Quotient.mk I.1 r) = 0 ↔ r ∈ I.1
    rw [e.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- Evaluation at the distinguished root gives the universal-property
bijection between homomorphisms from `ℤ[X]/(f)` and roots modulo `q`. -/
noncomputable def polynomialRootsEquivRingHoms (f : ℤ[X]) (q : ℕ) :
    {x : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) x = 0} ≃
      (AdjoinRoot f →+* ZMod q) where
  toFun x := AdjoinRoot.lift (Int.castRingHom (ZMod q)) x.1 x.2
  invFun φ := ⟨φ (AdjoinRoot.root f), by
    have h := f.hom_eval₂ (AdjoinRoot.of f) φ (AdjoinRoot.root f)
    rw [AdjoinRoot.eval₂_root, map_zero, RingHom.ext_int
      (φ.comp (AdjoinRoot.of f)) (Int.castRingHom (ZMod q))] at h
    exact h.symm⟩
  left_inv x := Subtype.ext (AdjoinRoot.lift_root x.2)
  right_inv φ := by
    apply AdjoinRoot.ringHom_ext (RingHom.ext_int _ _)
    exact AdjoinRoot.lift_root _

/-- Every residue root corresponds to one cyclic quotient ideal of the
polynomial order, and conversely. -/
noncomputable def polynomialRootsEquivQuotientIdeals (f : ℤ[X]) (q : ℕ) :
    {x : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) x = 0} ≃
      ZModQuotientIdeals (AdjoinRoot f) q :=
  (polynomialRootsEquivRingHoms f q).trans (ringHomsEquivZModQuotientIdeals _ q)

/-- The exact root-count/cyclic-quotient-ideal counting identity for the
polynomial order. It does not presume that this order is maximal. -/
theorem rootCount_polynomial_eq_card_quotientIdeals (f : ℤ[X]) (q : ℕ) [NeZero q] :
    rootCount (polynomialAbsValue f) q = Nat.card (ZModQuotientIdeals (AdjoinRoot f) q) := by
  rw [rootCount_polynomial_eq_card_zmod]
  exact Nat.card_congr (polynomialRootsEquivQuotientIdeals f q)

/-- A cyclic quotient ideal has index `q`. This uses the unbundled quotient
cardinality, so it also applies when the polynomial order is not Dedekind. -/
theorem cardQuot_zmodQuotientIdeal {R : Type*} [CommRing R] {q : ℕ} [NeZero q]
    (I : ZModQuotientIdeals R q) : Submodule.cardQuot I.1 = q := by
  obtain ⟨e⟩ := I.2
  rw [Submodule.cardQuot_apply, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- In a Dedekind order the bundled absolute norm is this same index. -/
theorem absNorm_zmodQuotientIdeal {R : Type*} [CommRing R] [Nontrivial R]
    [IsDedekindDomain R] [Module.Free ℤ R] {q : ℕ} [NeZero q]
    (I : ZModQuotientIdeals R q) : Ideal.absNorm I.1 = q := by
  rw [Ideal.absNorm_apply]
  exact cardQuot_zmodQuotientIdeal I

end Erdos975Support
