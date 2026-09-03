import Submission.AlgClosedLinearDisjoint

/-!
Relative algebraic closures on independent supports. These lemmas serve an
algebraic graph-covering argument; they do not settle Erdős 595.
-/
set_option autoImplicit false
open Set
open scoped TensorProduct
namespace Erdos595AlgebraicSupportFields

section Closure
variable (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L]

def closure (S : Set L) : IntermediateField F L :=
  (algebraicClosure (IntermediateField.adjoin F S) L).restrictScalars F

lemma mem_closure_iff {S : Set L} {x : L} :
    x ∈ closure F S ↔ IsAlgebraic (Algebra.adjoin F S) x := by
  exact mem_algebraicClosure_iff.trans IntermediateField.isAlgebraic_adjoin_iff

lemma subset_closure (S : Set L) : S ⊆ closure F S := by
  intro x hx
  apply (mem_closure_iff F).mpr
  exact isAlgebraic_algebraMap (R := Algebra.adjoin F S)
    (⟨x,Algebra.subset_adjoin hx⟩ : Algebra.adjoin F S)

lemma closure_mono {S T : Set L} (h : S ⊆ T) : closure F S ≤ closure F T := by
  intro x hx
  exact (mem_closure_iff F).mpr
    (((mem_closure_iff F).mp hx).tower_top_of_subalgebra_le (Algebra.adjoin_mono h))

instance closure_isAlgClosed [IsAlgClosed L] (S : Set L) : IsAlgClosed (closure F S) := by
  change IsAlgClosed (algebraicClosure (IntermediateField.adjoin F S) L)
  exact IsAlgClosure.isAlgClosed (IntermediateField.adjoin F S)

lemma closure_le (K : IntermediateField F L) [IsAlgClosed K] {S : Set L}
    (hS : S ⊆ K) : closure F S ≤ K := by
  intro x hx
  have hxK : IsAlgebraic K x :=
    ((mem_closure_iff F).mp hx).tower_top_of_subalgebra_le (Algebra.adjoin_le hS)
  have hm : x ∈ algebraicClosure K L := mem_algebraicClosure_iff.mpr hxK
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure K L)] at hm
  obtain ⟨y,hy⟩ := IntermediateField.mem_bot.mp hm
  exact hy ▸ y.property

/-- Adjoining generators after taking a relative algebraic closure does not
change the final relative algebraic closure. -/
theorem closure_rebase [IsAlgClosed L] (S T : Set L) :
    (closure (closure F S) T).restrictScalars F = closure F (S ∪ T) := by
  let K := closure F S
  let C := closure F (S ∪ T)
  have hKC : K ≤ C := closure_mono F subset_union_left
  let C' : IntermediateField K L := IntermediateField.extendScalars hKC
  haveI : IsAlgClosed C' := inferInstanceAs (IsAlgClosed C)
  apply le_antisymm
  · exact closure_le K C' (fun x hx => subset_closure F (S ∪ T) (Or.inr hx))
  · letI : IsAlgClosed ((closure K T).restrictScalars F) :=
      inferInstanceAs (IsAlgClosed (closure K T))
    apply closure_le F ((closure K T).restrictScalars F)
    intro x hx
    rcases hx with hx | hx
    · exact (closure K T).algebraMap_mem (⟨x,subset_closure F S hx⟩ : K)
    · exact subset_closure K T hx

lemma closure_eq_matroid (S : Set L) :
    (closure F S : Set L) = (AlgebraicIndependent.matroid F L).closure S := by
  ext x
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact mem_closure_iff F

/-- Finite character: a finite collection of elements of an algebraic closure
uses only finitely many of the independent generators. -/
theorem finite_support {I : Type*} {t : I → L} (ht : IsTranscendenceBasis F t)
    (X : Finset L) : ∃ S : Finset I, ∀ x ∈ X, x ∈ closure F (t '' (S : Set I)) := by
  classical
  let M := AlgebraicIndependent.matroid F L
  have hX : (X : Set L) ⊆ M.closure (range t) := by
    intro x _
    rw [← closure_eq_matroid F]
    exact (mem_closure_iff F).mpr (ht.isAlgebraic.isAlgebraic x)
  obtain ⟨Y,hY,hfin,_,hXY⟩ := Matroid.exists_subset_finite_closure_of_subset_closure
    X.finite_toSet hX
  have hpre : (t ⁻¹' Y).Finite := hfin.preimage ht.1.injective.injOn
  refine ⟨hpre.toFinset,?_⟩
  intro x hx
  rw [hpre.coe_toFinset,image_preimage_eq_of_subset hY]
  change x ∈ (closure F Y : Set L)
  rw [closure_eq_matroid]
  exact hXY hx

end Closure

section Independent
variable {F L I : Type*} [Field F] [Field L] [Algebra F L]
  {t : I → L} (ht : AlgebraicIndependent F t)
include ht

/-- Algebraic closure of one set of independent generators does not destroy
algebraic independence of a disjoint set. -/
theorem independent_over_closure {S T : Set I} (hST : Disjoint S T) :
    AlgebraicIndependent (closure F (t '' S)) (fun i : T => t i) := by
  have h : AlgebraicIndependent (IntermediateField.adjoin F (t '' S))
      (fun i : T => t i) :=
    IntermediateField.algebraicIndependent_adjoin_iff.mpr (ht.adjoin_of_disjoint hST)
  exact h.algebraicClosure

/-- Disjoint independent supports give actual injectivity, not merely an
abstract tensor-domain assertion. -/
theorem disjoint_mul_injective [IsAlgClosed F] {S T : Set I} (hST : Disjoint S T) :
    Function.Injective
      (Erdos595AlgClosedLinearDisjoint.mulHom F (closure F (t '' S)) (closure F (t '' T)) L) := by
  let B := closure F (t '' S)
  let A := closure F (t '' T)
  let x : S → B := fun i => ⟨t i,subset_closure F (t '' S) (mem_image_of_mem t i.property)⟩
  apply Erdos595AlgClosedLinearDisjoint.injective_of_algebraic_generators F B A L x
  · exact ht.comp Subtype.val Subtype.val_injective
  · intro b
    have hb := (mem_closure_iff F).mp b.property
    change IsAlgebraic (Algebra.adjoin F (range (fun i : S => t i))) (b : L)
    rw [← image_eq_range t S]
    exact hb
  · exact independent_over_closure ht hST.symm

/-- Mathlib's linearly disjoint formulation of the preceding result. -/
theorem disjoint_linearDisjoint [IsAlgClosed F] {S T : Set I} (hST : Disjoint S T) :
    (closure F (t '' S)).LinearDisjoint (closure F (t '' T)) := by
  rw [IntermediateField.linearDisjoint_iff',Subalgebra.linearDisjoint_iff_injective]
  exact disjoint_mul_injective ht hST

end Independent

#print axioms closure_rebase
#print axioms finite_support
#print axioms disjoint_mul_injective
#print axioms disjoint_linearDisjoint
end Erdos595AlgebraicSupportFields
