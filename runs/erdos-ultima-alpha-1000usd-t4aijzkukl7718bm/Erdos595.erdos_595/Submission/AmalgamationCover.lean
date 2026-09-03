import Submission.FiniteFolkmanAmalgamation
import Submission.FinitePaletteCompactness

/-!
Free amalgamation preserves countable triangle-free edge coverability.
This is a limitation of the partite route, not a settlement of Erdős 595.
No finiteness assumptions on carriers or on the family of copies are used.
-/

open SimpleGraph Set
namespace Erdos595AmalgamationCover
open Erdos595Work Erdos595FinitePalette Erdos595FiniteFolkmanAmalgamation

variable {A B I C : Type*} (H : SimpleGraph A) (K : SimpleGraph B)
    (D : Set A) (e : I → H.induce D ↪g K)

/-- Reuse the old palettes on both sorts of internal edges, reserving a
single new color for all edges crossing from the base to private vertices. -/
def color (cH : Sym2 A → C) (cK : Sym2 B → C) :
    Sym2 (Vertex D (B := B) (I := I)) → Option C :=
  Sym2.lift ⟨fun x y => match x,y with
    | .inl a,.inl b => some (cK s(a,b))
    | .inr a,.inr b => some (cH s(a.2.val,b.2.val))
    | _,_ => none,
    by intro x y; cases x <;> cases y <;> simp only [Sym2.eq_swap]⟩

/-- A single extra color suffices, even for an arbitrary family of copies. -/
theorem palette (hH : HasColoring H C) (hK : HasColoring K C) :
    HasColoring (graph H K D e) (Option C) := by
  obtain ⟨cH,hH⟩ := hH
  obtain ⟨cK,hK⟩ := hK
  refine ⟨color D cH cK,?_⟩
  intro a b d hab had hbd he
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases d with
      | inl d =>
        exact hK a b d hab had hbd ⟨Option.some.inj he.1,Option.some.inj he.2⟩
      | inr d => simp [color] at he
    | inr b =>
      cases d with
      | inl d => simp [color] at he
      | inr d => simp [color] at he
  | inr a =>
    cases b with
    | inl b =>
      cases d with
      | inl d => simp [color] at he
      | inr d => simp [color] at he
    | inr b =>
      cases d with
      | inl d => simp [color] at he
      | inr d =>
        exact hH a.2.val b.2.val d.2.val hab.2 had.2 hbd.2
          ⟨Option.some.inj he.1,Option.some.inj he.2⟩

/-- Countable covers cannot be destroyed by one free-amalgamation step. -/
theorem countable_cover
    (hH : IsCountableUnionOfTriangleFree H)
    (hK : IsCountableUnionOfTriangleFree K) :
    IsCountableUnionOfTriangleFree (graph H K D e) := by
  apply HasColoring.countable_cover (C := Option ℕ)
  exact palette H K D e
    (countable_union_iff_edge_coloring H |>.mp hH)
    (countable_union_iff_edge_coloring K |>.mp hK)

/-- If at least one copy is attached, both input graphs embed in the result,
so the preservation statement is an equivalence. -/
theorem countable_cover_iff [Nonempty I] :
    IsCountableUnionOfTriangleFree (graph H K D e) ↔
      IsCountableUnionOfTriangleFree H ∧ IsCountableUnionOfTriangleFree K := by
  refine ⟨fun h => ⟨?_,?_⟩,fun h => countable_cover H K D e h.1 h.2⟩
  · exact countable_union_of_hom
      (copyEmbedding H K D e (Classical.arbitrary I)).toHom h
  · exact countable_union_of_hom (baseEmbedding H K D e).toHom h

/-- With a triangle-free base, an amalgamation is countably coverable
exactly when the old graph is. This applies to the new half-graph P4 step. -/
theorem triangleFree_base_iff [Nonempty I] (hK : K.CliqueFree 3) :
    IsCountableUnionOfTriangleFree (graph H K D e) ↔
      IsCountableUnionOfTriangleFree H := by
  rw [countable_cover_iff]
  have hc : IsCountableUnionOfTriangleFree K :=
    ⟨fun _ => K,fun _ => hK,by simp only [iSup_const]⟩
  exact and_iff_left hc

#print axioms palette
#print axioms countable_cover_iff
#print axioms triangleFree_base_iff
end Erdos595AmalgamationCover
