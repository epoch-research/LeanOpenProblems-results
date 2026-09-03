import Submission.RightFiberCover
import Submission.SecondArcReflection

/-!
The exact TWO-step symmetrized arc/right round trip preserves countable
triangle-free edge coverability. This closes another possible amplification
route; it does not settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SecondArcCover
open Erdos595ArcAdjoint Erdos595ArcRoundTrip Erdos595Work

variable {V : Type*} (T : SimpleGraph V)

/-- Vertex subsets closed under moving along an edge in a triangle. -/
def TriangleClosed (S : Set V) : Prop :=
  ∀ a b c, T.Adj a b → T.Adj a c → T.Adj b c → a ∈ S → b ∈ S

/-- The profile is a quotient-free code for a triangle-connected component. -/
def component (a : V) : Set (Set V) := {S | TriangleClosed T S ∧ a ∈ S}

lemma component_triangle {a b c : V}
    (hab : T.Adj a b) (hac : T.Adj a c) (hbc : T.Adj b c) :
    component T a = component T b := by
  ext S
  constructor
  · rintro ⟨hS, ha⟩
    exact ⟨hS, hS a b c hab hac hbc ha⟩
  · rintro ⟨hS, hb⟩
    exact ⟨hS, hS b a c hab.symm hbc hac hb⟩

lemma component_connected (i : Set (Set V))
    (a₀ : {a : V // component T a = i})
    (P : {a : V // component T a = i} → Prop) (h₀ : P a₀)
    (hP : ∀ a b c : {a : V // component T a = i},
      T.Adj a.val b.val → T.Adj a.val c.val → T.Adj b.val c.val → P a → P b) :
    ∀ a, P a := by
  let S : Set V := {a | ∃ h : component T a = i, P ⟨a,h⟩}
  have hS : TriangleClosed T S := by
    intro a b c hab hac hbc ha
    obtain ⟨ha, hp⟩ := ha
    have hb : component T b = i := (component_triangle T hab hac hbc).symm.trans ha
    have hc : component T c = i := (component_triangle T hac hab hbc.symm).symm.trans ha
    exact ⟨hb, hP ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ hab hac hbc hp⟩
  have hm : S ∈ component T a₀.val := ⟨hS, a₀.property, h₀⟩
  intro a
  have he : component T a₀.val = component T a.val := a₀.property.trans a.property.symm
  rw [he] at hm
  obtain ⟨ha, hp⟩ := hm.2
  exact hp

/-- The component profiles confine every triangle to a fiber. -/
lemma component_fibers : Erdos595TriangleFiber.TrianglesInFibers T (component T) := by
  intro a b c hab hac hbc
  exact ⟨component_triangle T hab hac hbc, component_triangle T hac hab hbc.symm⟩

variable {W : Type*} (H : SimpleGraph W)

/-- After an arc/right round trip of a graph with unique triangle edges,
one more right adjoint preserves any cover of its original right adjoint. -/
theorem right_roundtrip_cover (hH : UniqueTriangleEdge H)
    (hc : IsCountableUnionOfTriangleFree (right H)) :
    IsCountableUnionOfTriangleFree (right (right (arcGraph H))) := by
  classical
  let T := right (arcGraph H)
  apply Erdos595RightFiber.cover_of_fibers T (component T) (component_fibers T)
  intro i
  let F := T.induce {a | component T a = i}
  by_cases hF : F.CliqueFree 3
  · apply right_cover_of_rainbow F (fun _ => (0 : Fin 1))
    intro a b c hab hac hbc
    exact (hF _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)).elim
  · let f := SimpleGraph.topEmbeddingOfNotCliqueFree hF
    have hadj : ∀ a b : Fin 3, a ≠ b → F.Adj (f a) (f b) :=
      fun a b h => f.map_rel_iff.mpr h
    let inc : F →g T := ⟨Subtype.val, fun h => h⟩
    obtain ⟨g⟩ := triangle_connected_hom H F (f 0)
      ⟨f 1, f 2, hadj 0 1 (by decide), hadj 0 2 (by decide), hadj 1 2 (by decide)⟩
      (component_connected T i (f 0)) hH inc
    exact countable_union_of_hom (Erdos595RightFiber.rightHom g) hc

/-- Countable covering cannot be destroyed by the TWO-step round trip. -/
theorem twice_cover (hG : IsCountableUnionOfTriangleFree T) :
    IsCountableUnionOfTriangleFree (right (right (arcGraph (arcGraph T)))) :=
  right_roundtrip_cover (arcGraph T) (arc_unique_triangle_edge T) (right_arc_cover T hG)

/-- The preservation statement is exact and needs no clique hypothesis. -/
theorem twice_cover_iff :
    IsCountableUnionOfTriangleFree (right (right (arcGraph (arcGraph T)))) ↔
      IsCountableUnionOfTriangleFree T :=
  ⟨Erdos595SecondArcReflection.source_cover_of_twice_cover T, twice_cover T⟩

#print axioms component_connected
#print axioms right_roundtrip_cover
#print axioms twice_cover_iff
end Erdos595SecondArcCover
