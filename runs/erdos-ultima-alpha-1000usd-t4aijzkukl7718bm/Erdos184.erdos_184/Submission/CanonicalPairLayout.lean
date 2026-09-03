import Submission.PairSlotMarkers
import Submission.NormalizedKernel

/-! Canonical sorted marker placements for two-incidence contact families. -/
open SimpleGraph
namespace Erdos184Work.CanonicalPairLayout
open PairJunctionCoding JunctionPairCoding PairSlotMarkers CycleSegments
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {l : ℕ}

def arity (b : PairIndex l → Fin 3) (i : Fin l) : ℕ := (markers b i).card - 2

def place (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
    (i : Fin l) : Fin (arity b i+2) → Fin ((l*l)*2) :=
  (markers b i).orderEmbOfFin (Nat.sub_add_cancel (hb i)).symm

lemma place_injective (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card) (i : Fin l) :
    Function.Injective (place b hb i) :=
  (markers b i).orderEmbOfFin (Nat.sub_add_cancel (hb i)).symm |>.injective

lemma place_strictMono (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card) (i : Fin l) :
    StrictMono (place b hb i) :=
  (markers b i).orderEmbOfFin (Nat.sub_add_cancel (hb i)).symm |>.strictMono

def successorDest {W : Type*} {n : Fin l → ℕ} (q : ∀ i, Fin (n i+2) → W)
    (o : ∀ i, Marked.Order (n i)) (j : Σ i, Fin (n i+2)) : W :=
  q j.1 (Marked.nextFin (n j.1) (o j.1) j.2)

section Actual
open scoped Classical
variable {V : Type*} [Fintype V] (B : Fin l → Set V)
    (htwo : ∀ w : Junction B, Nat.card {i : Fin l // w.val ∈ B i} = 2)
    (hbound : ∀ i j : Fin l, i ≠ j → (B i ∩ B j).ncard ≤ 2)
    (hcontacts : ∀ i, 2 ≤ Fintype.card (LocalJunction B i))
include hcontacts

lemma marker_card_lower (i : Fin l) :
    2 ≤ (markers (counts B htwo hbound) i).card := by
  rw [markers_card]
  exact hcontacts i

noncomputable def actualPlace (i : Fin l) :
    Fin (arity (counts B htwo hbound) i+2) → Junction B :=
  fun j => ((localMarkerEquiv B htwo hbound i).symm
    ((markers (counts B htwo hbound) i).orderIsoOfFin
      (Nat.sub_add_cancel (marker_card_lower B htwo hbound hcontacts i)).symm j)).val

lemma actualPlace_injective (i : Fin l) :
    Function.Injective (actualPlace B htwo hbound hcontacts i) := by
  intro x y h
  have h1 := Subtype.ext h
  have h2 := (localMarkerEquiv B htwo hbound i).symm.injective h1
  exact ((markers (counts B htwo hbound) i).orderIsoOfFin
    (Nat.sub_add_cancel (marker_card_lower B htwo hbound hcontacts i)).symm).injective h2

lemma actualPlace_code (i : Fin l) (j : Fin (arity (counts B htwo hbound) i+2)) :
    codeVertex B htwo hbound (actualPlace B htwo hbound hcontacts i j) =
      place (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) i j := by
  rw [actualPlace,← localMarkerEquiv_val,(localMarkerEquiv B htwo hbound i).apply_symm_apply]
  rfl

lemma actualPlace_range (i : Fin l) (w : Junction B) :
    w.val ∈ B i ↔ ∃ j, actualPlace B htwo hbound hcontacts i j = w := by
  constructor
  · intro hw
    let z : LocalJunction B i := ⟨w,hw⟩
    let e := (markers (counts B htwo hbound) i).orderIsoOfFin
      (Nat.sub_add_cancel (marker_card_lower B htwo hbound hcontacts i)).symm
    refine ⟨e.symm (localMarkerEquiv B htwo hbound i z),?_⟩
    change (((localMarkerEquiv B htwo hbound i).symm
      (e (e.symm (localMarkerEquiv B htwo hbound i z)))).val) = w
    rw [e.apply_symm_apply,Equiv.symm_apply_apply]
  · rintro ⟨j,rfl⟩
    exact ((localMarkerEquiv B htwo hbound i).symm
      ((markers (counts B htwo hbound) i).orderIsoOfFin
        (Nat.sub_add_cancel (marker_card_lower B htwo hbound hcontacts i)).symm j)).property

variable {G : SimpleGraph V} (root : Fin l → V) (C : ∀ i, G.Walk (root i) (root i))
    (hBC : ∀ i, B i = {x | x ∈ (C i).support})
include hBC

lemma actual_layout :
    ContactLayout (fun i => arity (counts B htwo hbound) i+2)
      (actualPlace B htwo hbound hcontacts) Subtype.val root C := by
  refine ⟨Subtype.val_injective,?_,?_⟩
  · intro i w
    have h := actualPlace_range B htwo hbound hcontacts i w
    rwa [hBC i] at h
  · intro i j hij x hxi hxj
    refine ⟨⟨x,i,j,hij,?_,?_⟩,rfl⟩
    · rwa [hBC i]
    · rwa [hBC j]

lemma exists_ordered_family (hC : ∀ i, (C i).IsCycle)
    (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ i, s(x,y) ∈ (C i).edges) :
    ∃ o : ∀ i, Marked.Order (arity (counts B htwo hbound) i),
    ∃ F : PathSubstitution.Family (Σ i, Fin (arity (counts B htwo hbound) i+2)) (Junction B) G,
      F.vertex = Subtype.val ∧
      F.src = (fun j => actualPlace B htwo hbound hcontacts j.1 j.2) ∧
      F.dst = successorDest (n := arity (counts B htwo hbound))
        (actualPlace B htwo hbound hcontacts) o ∧
      (∀ i e, e ∈ (C i).edges ↔ ∃ j, e ∈ (F.path ⟨i,j⟩).edges) ∧
      (∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :=
  ContactLayout.exists_ordered_family (arity (counts B htwo hbound))
    (actualPlace B htwo hbound hcontacts) (actualPlace_injective B htwo hbound hcontacts)
    Subtype.val root C hC (actual_layout B htwo hbound hcontacts root C hBC) hd hcover

#print axioms actualPlace_code
#print axioms exists_ordered_family
end Actual
end Erdos184Work.CanonicalPairLayout
