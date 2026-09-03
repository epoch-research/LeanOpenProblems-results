import Submission.KernelMarker

/-! Exact count three for every subdivision of the nonalternating
three-cycle kernel with contact multiplicities two, two, zero. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.NonAlternate220
open Erdos184Serial PathSubstitution
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma full_valid_any (i8 : DecidableEq (Fin 8)) (i4 : DecidableEq (Fin 4)) :
    (@LabelKernel.code (Fin 8) (Fin 4) i8 i4 src dst).valid Finset.univ := by
  have h8 : i8 = instDecidableEqFin 8 := Subsingleton.elim _ _
  have h4 : i4 = instDecidableEqFin 4 := Subsingleton.elim _ _
  subst i8
  subst i4
  exact full_valid

lemma full_number_any (i8 : DecidableEq (Fin 8)) (i4 : DecidableEq (Fin 4)) :
    @HasNumber (Fin 8) i8 (@LabelKernel.code (Fin 8) (Fin 4) i8 i4 src dst) Finset.univ 3 := by
  have h8 : i8 = instDecidableEqFin 8 := Subsingleton.elim _ _
  have h4 : i4 = instDecidableEqFin 4 := Subsingleton.elim _ _
  subst i8
  subst i4
  exact full_number

lemma subdivision_number_three (F : Family (Fin 8) (Fin 4) G)
    (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G = 3 := by
  have hK : @HasNumber (Fin 8) (Classical.decEq _)
      (@LabelKernel.code (Fin 8) (Fin 4) (Classical.decEq _) (Classical.decEq _) F.src F.dst) Finset.univ 3 := by
    rw [hs,ht]
    exact full_number_any _ _
  have hv : F.validLabels Finset.univ := by
    unfold Family.validLabels
    rw [hs,ht]
    exact full_valid_any (Classical.decEq _) (Classical.decEq _)
  have he : ∀ x, Even (G.degree x) := by
    have he' := (F.expandGraph_even_iff _).mpr hv
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he' ⊢
    rwa [F.expandGraph_univ hcover] at he'
  exact (F.number_iff_kernel_full hcover he 3).mpr hK

#print axioms subdivision_number_three
end Erdos184Work.NonAlternate220
