import Submission.AlgebraicSupportFields

/-!
A countable algebraically closed field with countably infinite transcendence
basis is universal for countable field extensions of its coefficient field.
This is auxiliary to the algebraic graph-covering route.
-/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
open Set
namespace Erdos595CountableFieldUniversal

section Cardinality
variable (R E : Type*) [CommRing R] [IsDomain R] [CommRing E] [IsDomain E]
  [Algebra R E] [Module.IsTorsionFree R E] [Algebra.IsAlgebraic R E]

lemma countable_algebraic [Countable R] : Countable E := by
  apply Cardinal.mk_le_aleph0_iff.mp
  have h := Algebra.IsAlgebraic.lift_cardinalMk_le_max R E
  have hr : Cardinal.lift (Cardinal.mk R) ≤ Cardinal.aleph0 := by
    simpa using (Cardinal.lift_le.mpr (Cardinal.mk_le_aleph0 (α := R)))
  have he := h.trans (max_le hr le_rfl)
  simpa using he

end Cardinality

section Adjoin
variable (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L] [Countable F]

lemma countable_adjoin (S : Set L) (hS : S.Countable) :
    Countable (IntermediateField.adjoin F S) := by
  letI : Countable S := hS.to_subtype
  apply Cardinal.mk_le_aleph0_iff.mp
  have h := IntermediateField.lift_cardinalMk_adjoin_le F S
  have hr : Cardinal.lift (Cardinal.mk F) ≤ Cardinal.aleph0 := by
    simpa using (Cardinal.lift_le.mpr (Cardinal.mk_le_aleph0 (α := F)))
  have hs : Cardinal.lift (Cardinal.mk S) ≤ Cardinal.aleph0 := by
    simpa using (Cardinal.lift_le.mpr (Cardinal.mk_le_aleph0 (α := S)))
  have he := h.trans (max_le (max_le hr hs) le_rfl)
  simpa using he

lemma countable_closure (S : Set L) (hS : S.Countable) :
    Countable (Erdos595AlgebraicSupportFields.closure F S) := by
  change Countable (algebraicClosure (IntermediateField.adjoin F S) L)
  letI := countable_adjoin F S hS
  exact countable_algebraic (IntermediateField.adjoin F S) _

end Adjoin

section Omega
variable (F : Type*) [Field F]

abbrev Omega := AlgebraicClosure (FractionRing (MvPolynomial ℕ F))

instance omega_isAlgClosed : IsAlgClosed (Omega F) :=
  IsAlgClosure.isAlgClosed (FractionRing (MvPolynomial ℕ F))

instance omega_countable [Countable F] : Countable (Omega F) := by
  letI : Countable (MvPolynomial ℕ F) := inferInstanceAs (Countable ((ℕ →₀ ℕ) →₀ F))
  letI : Module.IsTorsionFree (MvPolynomial ℕ F) (FractionRing (MvPolynomial ℕ F)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsFractionRing.injective (MvPolynomial ℕ F) (FractionRing (MvPolynomial ℕ F)))
  letI : Algebra.IsAlgebraic (MvPolynomial ℕ F) (FractionRing (MvPolynomial ℕ F)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial ℕ F))
  letI : Countable (FractionRing (MvPolynomial ℕ F)) := countable_algebraic (MvPolynomial ℕ F) _
  exact countable_algebraic (FractionRing (MvPolynomial ℕ F)) _

noncomputable def generators : ℕ → Omega F := fun n =>
  algebraMap (MvPolynomial ℕ F) (Omega F) (MvPolynomial.X n)

lemma generators_independent : AlgebraicIndependent F (generators F) := by
  apply (MvPolynomial.algebraicIndependent_X ℕ F).map'
    (f := IsScalarTower.toAlgHom F (MvPolynomial ℕ F) (Omega F))
  exact (RingHom.injective (algebraMap (FractionRing (MvPolynomial ℕ F)) (Omega F))).comp
    (IsFractionRing.injective (MvPolynomial ℕ F) (FractionRing (MvPolynomial ℕ F)))

/-- Every countable field extension embeds over F into one fixed field Omega F. -/
theorem exists_hom (E : Type*) [Field E] [Algebra F E] [Countable E] :
    Nonempty (E →ₐ[F] Omega F) := by
  classical
  obtain ⟨S,hS⟩ := exists_isTranscendenceBasis F E
  obtain ⟨idx,hidx⟩ := exists_injective_nat S
  let t : S → E := Subtype.val
  let w : S → Omega F := fun i => generators F (idx i)
  have hw : AlgebraicIndependent F w := (generators_independent F).comp idx hidx
  let P := MvPolynomial S F
  letI : Algebra P E := (MvPolynomial.aeval t : P →ₐ[F] E).toRingHom.toAlgebra
  letI : IsScalarTower F P E := IsScalarTower.of_algebraMap_eq fun r =>
    ((MvPolynomial.aeval t : P →ₐ[F] E).commutes r).symm
  letI : Algebra P (Omega F) := (MvPolynomial.aeval w : P →ₐ[F] Omega F).toRingHom.toAlgebra
  letI : IsScalarTower F P (Omega F) := IsScalarTower.of_algebraMap_eq fun r =>
    ((MvPolynomial.aeval w : P →ₐ[F] Omega F).commutes r).symm
  let C := Algebra.adjoin F (range t)
  let e : P ≃ₐ[F] C := hS.1.aevalEquiv
  letI : Algebra.IsAlgebraic C E := hS.isAlgebraic
  letI : Algebra.IsAlgebraic P E :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq e (RingHom.id E) e.surjective
      Function.injective_id (by
        apply RingHom.ext
        intro p
        exact hS.1.algebraMap_aevalEquiv p)
  letI : Module.IsTorsionFree P E := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (algebraicIndependent_iff_injective_aeval.mp hS.1)
  letI : Module.IsTorsionFree P (Omega F) := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (algebraicIndependent_iff_injective_aeval.mp hw)
  exact ⟨(IsAlgClosed.lift (R := P) (S := E) (M := Omega F)).restrictScalars F⟩

end Omega

#print axioms countable_algebraic
#print axioms countable_closure
#print axioms omega_countable
#print axioms generators_independent
#print axioms exists_hom
end Erdos595CountableFieldUniversal
