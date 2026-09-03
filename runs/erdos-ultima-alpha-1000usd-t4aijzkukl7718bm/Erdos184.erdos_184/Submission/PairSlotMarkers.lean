import Submission.JunctionPairCoding

/-! Computable lists of the pair-slots incident to each color. -/
namespace Erdos184Work.PairSlotMarkers
open PairJunctionCoding JunctionPairCoding CycleSegments
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

variable {l : ℕ}

def markers (b : PairIndex l → Fin 3) (i : Fin l) : Finset (Fin ((l*l)*2)) :=
  Finset.univ.biUnion fun p : PairIndex l =>
    if i ∈ pairSet p then
      (Finset.univ.filter fun r : Fin 2 => r.val < (b p).val).image (fun r => slot (p,r))
    else ∅

lemma mem_markers (b : PairIndex l → Fin 3) (i : Fin l) (z : Fin ((l*l)*2)) :
    z ∈ markers b i ↔ ∃ p : PairIndex l, ∃ r : Fin 2,
      i ∈ pairSet p ∧ r.val < (b p).val ∧ slot (p,r) = z := by
  constructor
  · intro hz
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hz
    by_cases hi : i ∈ pairSet p
    · rw [if_pos hi] at hp
      obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hp
      exact ⟨p,r,hi,(Finset.mem_filter.mp hr).2,he⟩
    · rw [if_neg hi] at hp
      exact (Finset.notMem_empty z hp).elim
  · rintro ⟨p,r,hi,hr,he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p,Finset.mem_univ _,?_⟩
    rw [if_pos hi]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,he⟩

section Junctions
open scoped Classical
variable {V : Type*} [Fintype V] (B : Fin l → Set V)
    (htwo : ∀ w : Junction B, Nat.card {i : Fin l // w.val ∈ B i} = 2)
    (hbound : ∀ i j : Fin l, i ≠ j → (B i ∩ B j).ncard ≤ 2)

lemma markers_range (i : Fin l) (z : Fin ((l*l)*2)) :
    z ∈ markers (counts B htwo hbound) i ↔
      ∃ w : Junction B, codeVertex B htwo hbound w = z ∧ w.val ∈ B i := by
  rw [mem_markers]
  constructor
  · rintro ⟨p,r,hi,hr,rfl⟩
    obtain ⟨w,hw⟩ := (slot_range B htwo hbound p r).mpr hr
    refine ⟨w,hw,?_⟩
    rw [codeVertex_incidence B htwo hbound,hw,decodedPair_slot]
    simpa only [pairSet,Finset.mem_insert,Finset.mem_singleton] using hi
  · rintro ⟨w,rfl,hw⟩
    let e := fiberNumbering (incidence B) (incidence_two B htwo)
    let p := (e w).1
    let r : Fin 2 := Fin.castLE (multiplicity_le B htwo hbound p) (e w).2
    have he : codeVertex B htwo hbound w = slot (p,r) := rfl
    refine ⟨p,r,?_,(e w).2.isLt,he.symm⟩
    have hi := (codeVertex_incidence B htwo hbound w i).mp hw
    rw [he,decodedPair_slot] at hi
    simpa only [pairSet,Finset.mem_insert,Finset.mem_singleton] using hi

noncomputable def localMarkerEquiv (i : Fin l) : LocalJunction B i ≃
    (markers (counts B htwo hbound) i) :=
  Equiv.ofBijective (fun w => ⟨codeVertex B htwo hbound w.val,
    (markers_range B htwo hbound i _).mpr ⟨w.val,rfl,w.property⟩⟩) (by
      constructor
      · intro x y h
        apply Subtype.ext
        exact (codeVertex B htwo hbound).injective (congrArg Subtype.val h)
      · intro z
        obtain ⟨w,hw,hwi⟩ := (markers_range B htwo hbound i z.val).mp z.property
        exact ⟨⟨w,hwi⟩,Subtype.ext hw⟩)

lemma localMarkerEquiv_val (i : Fin l) (w : LocalJunction B i) :
    (localMarkerEquiv B htwo hbound i w).val = codeVertex B htwo hbound w.val := rfl

lemma markers_card (i : Fin l) : (markers (counts B htwo hbound) i).card =
    Fintype.card (LocalJunction B i) := by
  have h := Fintype.card_congr (localMarkerEquiv B htwo hbound i)
  simpa only [Fintype.card_coe] using h.symm

noncomputable def orderedPlace (i : Fin l)
    (j : Fin (markers (counts B htwo hbound) i).card) : Junction B :=
  ((localMarkerEquiv B htwo hbound i).symm
    ((markers (counts B htwo hbound) i).orderIsoOfFin rfl j)).val

lemma orderedPlace_injective (i : Fin l) : Function.Injective (orderedPlace B htwo hbound i) := by
  intro j k h
  have h1 := Subtype.ext h
  have h2 := (localMarkerEquiv B htwo hbound i).symm.injective h1
  exact (markers (counts B htwo hbound) i).orderIsoOfFin rfl |>.injective h2

lemma orderedPlace_code (i : Fin l) (j : Fin (markers (counts B htwo hbound) i).card) :
    codeVertex B htwo hbound (orderedPlace B htwo hbound i j) =
      (markers (counts B htwo hbound) i).orderEmbOfFin rfl j := by
  rw [orderedPlace,← localMarkerEquiv_val,(localMarkerEquiv B htwo hbound i).apply_symm_apply]
  rfl

lemma orderedPlace_range (i : Fin l) (w : Junction B) :
    w.val ∈ B i ↔ ∃ j, orderedPlace B htwo hbound i j = w := by
  constructor
  · intro hw
    let t : LocalJunction B i := ⟨w,hw⟩
    refine ⟨((markers (counts B htwo hbound) i).orderIsoOfFin rfl).symm
      (localMarkerEquiv B htwo hbound i t),?_⟩
    simp only [orderedPlace,OrderIso.apply_symm_apply,Equiv.symm_apply_apply]
    rfl
  · rintro ⟨j,rfl⟩
    exact ((localMarkerEquiv B htwo hbound i).symm
      ((markers (counts B htwo hbound) i).orderIsoOfFin rfl j)).property

#print axioms orderedPlace_code
#print axioms orderedPlace_range
end Junctions
end Erdos184Work.PairSlotMarkers
