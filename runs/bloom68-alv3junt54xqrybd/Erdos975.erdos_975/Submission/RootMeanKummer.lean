import Submission.RootMeanIdeals

/-!
# The good-prime root/ideal coefficient identity

Mathlib's Kummer–Dedekind quotient isomorphism identifies the polynomial
quotient modulo a good prime with the maximal order modulo that prime.
Passing to homomorphisms into `ZMod p`, and then to their kernels, gives
an actual bijection between roots of `minpoly ℤ θ` modulo `p` and cyclic
quotient ideals of `𝓞 K`. A quotient of prime cardinality is necessarily
`ZMod p`, so these are exactly the ideals of absolute norm `p`.

This proves the equality of the prime coefficients needed by an Euler
correction argument. It does not assert the prime-power bounds or the
convergence of that correction.
-/

namespace Erdos975Support

open Polynomial NumberField

/-- Transport ring homomorphisms by an isomorphism of their source rings. -/
def ringHomsCongrSource {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) : (R →+* T) ≃ (S →+* T) where
  toFun φ := φ.comp e.symm.toRingHom
  invFun ψ := ψ.comp e.toRingHom
  left_inv φ := by ext r; simp
  right_inv ψ := by ext s; simp

/-- Every map into `ZMod q` factors uniquely through reduction modulo `q`. -/
def ringHomsQuotientSpanEquiv (R : Type*) [CommRing R] (q : ℕ) :
    (R →+* ZMod q) ≃ ((R ⧸ Ideal.span {(q : R)}) →+* ZMod q) where
  toFun φ := Ideal.Quotient.lift _ φ (fun r hr ↦ by
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
    simp only [map_mul, map_natCast, ZMod.natCast_self, zero_mul])
  invFun ψ := ψ.comp (Ideal.Quotient.mk _)
  left_inv φ := by ext r; rfl
  right_inv ψ := by apply Ideal.Quotient.ringHom_ext; ext r; rfl

/-- The root/homomorphism universal property for a polynomial already over
`ZMod q`. The coefficient map is unique because the base ring is cyclic. -/
noncomputable def zmodPolynomialRootsEquivRingHoms {q : ℕ} (F : (ZMod q)[X]) :
    {x : ZMod q // F.eval x = 0} ≃ (AdjoinRoot F →+* ZMod q) where
  toFun x := AdjoinRoot.lift (RingHom.id _) x.1 (by simpa only [eval₂_id] using x.2)
  invFun φ := ⟨φ (AdjoinRoot.root F), by
    have h := F.hom_eval₂ (AdjoinRoot.of F) φ (AdjoinRoot.root F)
    rw [AdjoinRoot.eval₂_root, map_zero,
      Subsingleton.elim (φ.comp (AdjoinRoot.of F)) (RingHom.id (ZMod q)), eval₂_id] at h
    exact h.symm⟩
  left_inv x := Subtype.ext (AdjoinRoot.lift_root _)
  right_inv φ := by
    apply AdjoinRoot.ringHom_ext (Subsingleton.elim _ _)
    exact AdjoinRoot.lift_root _

/-- Good-prime Kummer–Dedekind, in the cyclic quotient ideal form appropriate
for residue root counts. Only Mathlib's conductor/exponent hypothesis is used. -/
noncomputable def minpolyRootsEquivZModQuotientIdeals {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    {x : ZMod p // (minpoly ℤ θ).eval₂ (Int.castRingHom (ZMod p)) x = 0} ≃
      ZModQuotientIdeals (𝓞 K) p := by
  let F := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  let e₀ : {x : ZMod p // (minpoly ℤ θ).eval₂ (Int.castRingHom (ZMod p)) x = 0} ≃
      {x : ZMod p // F.eval x = 0} :=
    Equiv.subtypeEquivRight (fun x ↦ by rw [eval_map])
  let eK : AdjoinRoot F ≃+* (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) :=
    RingOfIntegers.ZModXQuotSpanEquivQuotSpan hp
  exact e₀.trans ((zmodPolynomialRootsEquivRingHoms F).trans
    ((ringHomsCongrSource eK).trans ((ringHomsQuotientSpanEquiv (𝓞 K) p).symm.trans
      (ringHomsEquivZModQuotientIdeals (𝓞 K) p))))

/-- Prime absolute norm is equivalent to having the cyclic prime residue
ring as quotient. This is stronger than only proving one direction of the
cyclic-quotient/ideal-norm correspondence. -/
theorem nonempty_quotientEquiv_zmod_prime_iff {R : Type*} [CommRing R] [Nontrivial R]
    [IsDedekindDomain R] [Module.Free ℤ R] (I : Ideal R) (p : ℕ) (hp : p.Prime) :
    Nonempty (R ⧸ I ≃+* ZMod p) ↔ Ideal.absNorm I = p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro he
    exact absNorm_zmodQuotientIdeal ⟨I, he⟩
  · intro hnorm
    have hcard : Nat.card (R ⧸ I) = p := by
      simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hnorm
    letI : Finite (R ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    letI : Fintype (R ⧸ I) := Fintype.ofFinite _
    have hfin : Fintype.card (R ⧸ I) = p := by rwa [Nat.card_eq_fintype_card] at hcard
    exact ⟨(ZMod.ringEquivOfPrime (R ⧸ I) hp hfin).symm⟩

/-- The prime coefficient identity: at every prime outside the conductor,
the root count of the integral minimal polynomial equals the number of ideals
of absolute norm that prime. -/
theorem rootCount_minpoly_eq_card_absNorm_prime {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    rootCount (polynomialAbsValue (minpoly ℤ θ)) p =
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p} := by
  rw [rootCount_polynomial_eq_card_zmod]
  apply Nat.card_congr
  exact (minpolyRootsEquivZModQuotientIdeals θ p hp).trans
    (Equiv.subtypeEquivRight (fun I ↦ nonempty_quotientEquiv_zmod_prime_iff I p
      (Fact.out : p.Prime)))

end Erdos975Support
