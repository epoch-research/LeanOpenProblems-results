import Submission.ProgressionFiberEquivalence

/-! Restricting a partial partition to a subset while retaining only complete
fibers. Points in an inner subset ensure that a coarse fiber is retained. -/
namespace Erdos3RestrictedPartialPartition
open Finset Erdos3FinitePartitionIncrement Erdos3ProgressionFiberEquivalence
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {V I : Type*} [Fintype V]

noncomputable def restrictLabel (B : Finset V) (c : V → Option I) (x : B) : Option I :=
  (c x).bind (fun i ↦ if cell c (some i) ⊆ B then some i else none)

lemma restrictLabel_some_iff (B : Finset V) (c : V → Option I) (x : B) (i : I) :
    restrictLabel B c x = some i ↔ c x = some i ∧ cell c (some i) ⊆ B := by
  unfold restrictLabel
  cases hx : c x with
  | none => simp
  | some j =>
    simp only [Option.bind_some]
    split_ifs with hj
    · simp only [Option.some.injEq]
      constructor
      · intro he
        subst j
        exact ⟨rfl,hj⟩
      · exact fun h ↦ h.1
    · simp only [reduceCtorEq,false_iff,not_and]
      intro he
      cases he
      exact hj

/-- Retained fibers are exactly the original complete fibers, with only the
ambient type changed from V to the subtype B. -/
noncomputable def restrictFiberEquiv (B : Finset V) (c : V → Option I) (i : I)
    (hi : cell c (some i) ⊆ B) : cell c (some i) ≃ cell (restrictLabel B c) (some i) where
  toFun x := ⟨⟨x.val,hi x.property⟩,(mem_cell_iff _ _ _).mpr
    ((restrictLabel_some_iff B c _ i).mpr ⟨(mem_cell_iff _ _ _).mp x.property,hi⟩)⟩
  invFun x := ⟨x.val.val,(mem_cell_iff _ _ _).mpr
    (((restrictLabel_some_iff B c _ i).mp ((mem_cell_iff _ _ _).mp x.property)).1)⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl

lemma restrictLabel_cell_card (B : Finset V) (c : V → Option I) (i : I)
    (hi : cell c (some i) ⊆ B) :
    (cell (restrictLabel B c) (some i)).card = (cell c (some i)).card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (restrictFiberEquiv B c i hi)).symm

/-- Boundary loss is additive: the restricted exceptional set contains at
most the old exceptional points plus the boundary B minus the inner subset. -/
theorem restrictLabel_bad_card (B B' : Finset V) (c : V → Option I)
    (hwhole : ∀ x ∈ B', ∀ i, c x = some i → cell c (some i) ⊆ B) :
    (cell (restrictLabel B c) none).card ≤ (cell c none).card+(B \ B').card := by
  have hmap : Set.MapsTo (fun x : B ↦ x.val) (cell (restrictLabel B c) none : Set B)
      (↑((cell c none) ∪ (B \ B') : Finset V) : Set V) := by
    intro x hx
    have hnone := (mem_cell_iff _ _ _).mp hx
    cases hc : c x.val with
    | none => exact mem_union_left _ ((mem_cell_iff _ _ _).mpr hc)
    | some i =>
      refine mem_union_right _ (mem_sdiff.mpr ⟨x.property,?_⟩)
      intro hx'
      have hs := (restrictLabel_some_iff B c x i).mpr ⟨hc,hwhole x hx' i hc⟩
      rw [hs] at hnone
      cases hnone
  exact (card_le_card_of_injOn (fun x : B ↦ x.val) hmap
    (fun _ _ _ _ h ↦ Subtype.val_injective h)).trans (card_union_le _ _)

#print axioms restrictFiberEquiv
#print axioms restrictLabel_bad_card
end Erdos3RestrictedPartialPartition
