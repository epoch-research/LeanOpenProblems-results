import Submission.CanonicalLocalBounds
import Submission.IndexedKernelRestrictions

/-! Extracting local bounds, without a full-support minimality hypothesis,
and transferring a two-circuit canonical partition back to the graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CanonicalLocalExtraction
open Erdos184Serial Critical MaximumCycles MaximumCoreFamilies CycleSegments
open PairJunctionCoding JunctionPairCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel
open LabelKernel CanonicalThreeReduction
set_option maxHeartbeats 3000000
set_option Elab.async false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {l : ℕ}
  (B : Fin l → Set V)
  (htwo : ∀ w : Junction B, Nat.card {i : Fin l // w.val ∈ B i} = 2)
  (hbound : ∀ i j : Fin l, i ≠ j → (B i ∩ B j).ncard ≤ 2)
  (hcontacts : ∀ i, 2 ≤ Fintype.card (LocalJunction B i))
  (root : Fin l → V) (C : ∀ i, G.Walk (root i) (root i))
  (hC : ∀ i, (C i).IsCycle)
  (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)
  (o : ∀ i, Marked.Order (arity (counts B htwo hbound) i))

noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

variable (F : PathSubstitution.Family (Σ i, Fin (arity (counts B htwo hbound) i+2)) (Junction B) G)
  (hsrc : F.src = (fun j => actualPlace B htwo hbound hcontacts j.1 j.2))
  (hdst : F.dst = successorDest (n := arity (counts B htwo hbound))
    (actualPlace B htwo hbound hcontacts) o)
  (hpiece : ∀ i e, e ∈ (C i).edges ↔ ∃ j, e ∈ (F.path ⟨i,j⟩).edges)
  (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges)

include hC hd F hsrc hdst hpiece hcover

lemma localBounds_of_family {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hwalk : Function.Injective (fun i => (C i).toSubgraph))
    (hmem : ∀ i, (C i).toSubgraph ∈ D)
    (hthree : ∀ A : Finset (Fin l), A.card = 3 →
      number (subfamilyGraph (A.image (fun i => (C i).toSubgraph))) ≤ 2) :
    LocalBounds (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o := by
  have hsub (A : Finset (Fin l)) : A.image (fun i => (C i).toSubgraph) ⊆ D := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact hmem i
  have hcard (A : Finset (Fin l)) : (A.image (fun i => (C i).toSubgraph)).card = A.card :=
    Finset.card_image_of_injective A hwalk
  constructor
  · intro A
    have hh : ∀ P, Partition (code F.src F.dst) (PathSubstitution.Family.colorLabels A) P → P.card ≤ A.card := by
      apply (F.color_maximum_bound_iff root C hpiece hcover A A.card).mp
      intro E hE hdE
      have hb := hD.subfamily_bound (A.image (fun i => (C i).toSubgraph)) (hsub A) E hE hdE
      rwa [hcard A] at hb
    rw [hsrc,hdst] at hh
    exact (normalized_upper_iff B htwo hbound hcontacts o A A.card).mp
      ((NormalizedKernel.upper_colors_iff (actualPlace B htwo hbound hcontacts) o A A.card).mp hh)
  · intro A hA
    have hn := (F.color_number_iff root C hC hd hpiece hcover A
      (number (subfamilyGraph (A.image (fun i => (C i).toSubgraph))))).mp rfl
    obtain ⟨P,hP,hcP⟩ := hn.1
    have hh : ∃ P, Partition (code F.src F.dst) (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ 2 :=
      ⟨P,hP,hcP.trans_le (hthree A hA)⟩
    rw [hsrc,hdst] at hh
    exact (normalized_exists_iff B htwo hbound hcontacts o A 2).mp
      ((NormalizedKernel.exists_colors_iff (actualPlace B htwo hbound hcontacts) o A 2).mp hh)

lemma number_le_of_two
    (h : ∃ P, Partition
      (code (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
        (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o))
      Finset.univ P ∧ P.card = 2) :
    number (subfamilyGraph (Finset.univ.image (fun i => (C i).toSubgraph))) ≤ 2 := by
  have hu : PathSubstitution.Family.colorLabels (Finset.univ : Finset (Fin l)) =
      (Finset.univ : Finset (Σ i, Fin (arity (counts B htwo hbound) i+2))) := by
    ext e
    simp [PathSubstitution.Family.colorLabels]
  have hh : ∃ P, Partition
      (code (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
        (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o))
      (PathSubstitution.Family.colorLabels Finset.univ) P ∧ P.card ≤ 2 := by
    rw [hu]
    obtain ⟨P,hP,hcP⟩ := h
    exact ⟨P,hP,hcP.le⟩
  have hraw := (NormalizedKernel.exists_colors_iff (actualPlace B htwo hbound hcontacts) o Finset.univ 2).mpr
    ((normalized_exists_iff B htwo hbound hcontacts o Finset.univ 2).mpr hh)
  change ∃ P, Partition (code (fun j : Σ i, Fin (arity (counts B htwo hbound) i+2) => actualPlace B htwo hbound hcontacts j.1 j.2)
    (successorDest (n := arity (counts B htwo hbound)) (actualPlace B htwo hbound hcontacts) o))
    (PathSubstitution.Family.colorLabels Finset.univ) P ∧ P.card ≤ 2 at hraw
  rw [← hsrc,← hdst] at hraw
  obtain ⟨P,hP,hcP⟩ := hraw
  have hn := (F.color_number_iff root C hC hd hpiece hcover Finset.univ
    (number (subfamilyGraph (Finset.univ.image (fun i => (C i).toSubgraph))))).mp rfl
  exact (hn.2 P hP).trans hcP

#print axioms localBounds_of_family
#print axioms number_le_of_two
end Erdos184Work.CanonicalLocalExtraction
