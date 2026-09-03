import Submission.BoundaryPrescribedExtension
import Submission.TransfiniteAmalgamationCover

/-!
A transfinite preservation theorem without the earlier triangle-free-base
restriction. This is not a proof or disproof of Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595TransfiniteBoundaryAmalgamation
open Erdos595FiniteAdapted Erdos595TransfiniteAmalgamation

universe u v
variable {V : Type u} {I : Type v} [LinearOrder I]
    (G : SimpleGraph V) (r : V → I)

open Erdos595FiniteFolkmanAmalgamation in
/-- A single stage is a free amalgam, with its distinguished copy identified
with the literal strict predecessor subgraph of the final graph. -/
structure AmalgamationStage (i : I) where
  B : Type u
  J : Type u
  K : SimpleGraph B
  D : Set (Earlier r i)
  embeddings : J → (earlierGraph G r i).induce D ↪g K
  distinguished : J
  iso : graph (earlierGraph G r i) K D embeddings ≃g throughGraph G r i
  old_eq : ∀ a, iso (copy (earlierGraph G r i) K D embeddings distinguished a) = inclusion r i a

namespace AmalgamationStage
open Erdos595FiniteFolkmanAmalgamation
variable {G r} {i : I} (s : AmalgamationStage G r i)

private theorem transfer
    (h : ∀ c : Sym2 (Earlier r i) → ℕ, Valid (earlierGraph G r i) c →
      ∃ d : Sym2 (Vertex s.D (B := s.B) (I := s.J)) → ℕ,
        Valid (graph (earlierGraph G r i) s.K s.D s.embeddings) d ∧
          ∀ a b, d s(copy (earlierGraph G r i) s.K s.D s.embeddings s.distinguished a,
            copy (earlierGraph G r i) s.K s.D s.embeddings s.distinguished b) = c s(a,b)) :
    StageExtension G r i := by
  intro c hc
  obtain ⟨d,hd,he⟩ := h c hc
  refine ⟨fun e => d (e.map s.iso.symm),?_,?_⟩
  · intro a b z hab haz hbz hm
    exact hd (s.iso.symm a) (s.iso.symm b) (s.iso.symm z)
      (s.iso.symm.map_rel_iff.mpr hab) (s.iso.symm.map_rel_iff.mpr haz)
      (s.iso.symm.map_rel_iff.mpr hbz) hm
  · intro a b
    change d s(s.iso.symm (inclusion r i a),s.iso.symm (inclusion r i b)) = c s(a,b)
    rw [← s.old_eq a,← s.old_eq b]
    simpa using he a b

/-- Literal extension does not require a triangle-free base. -/
theorem countably_colorable_extension (hK : Nonempty (s.K.Coloring ℕ)) :
    StageExtension G r i := by
  apply s.transfer
  intro c hc
  exact Erdos595BoundaryExtension.amalgamation
    (earlierGraph G r i) s.K s.D s.embeddings s.distinguished c hc hK

end AmalgamationStage

/-- Continuous well-ordered free amalgamation with countably properly
vertex-colorable bases preserves countable triangle-free edge covering.
The bases may contain triangles, and attachments can have arbitrary size. -/
theorem cover [WellFoundedLT I]
    (h : ∀ i, (IsEmpty (Earlier r i) ∧
        Erdos595Work.IsCountableUnionOfTriangleFree (throughGraph G r i)) ∨
      ∃ s : AmalgamationStage G r i, Nonempty (s.K.Coloring ℕ)) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  apply cover_of_stage_extensions G r
  intro i
  rcases h i with ⟨hi,hc⟩ | ⟨s,hs⟩
  · letI := hi
    exact initial_stage_extension G r i hc
  · exact s.countably_colorable_extension hs

#print axioms AmalgamationStage.countably_colorable_extension
#print axioms cover
end Erdos595TransfiniteBoundaryAmalgamation
