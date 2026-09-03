import Submission.UnusedColorAmalgamationExtension
import Submission.WellOrderedColorExtension

/-!
Continuous well-ordered amalgamation presentations preserve countable
triangle-free edge covers when the individual steps preserve prescribed
colorings. This connects the earlier local amalgamation extension lemmas to
an actual graph-level transfinite theorem. It does not settle Erdős 595.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595TransfiniteAmalgamation
open Erdos595FiniteAdapted

universe u v
variable {V : Type u} {I : Type v} [LinearOrder I]
    (G : SimpleGraph V) (r : V → I)

abbrev Earlier (i : I) := {a : V // r a < i}
abbrev Through (i : I) := {a : V // r a ≤ i}

abbrev earlierGraph (i : I) := G.induce {a | r a < i}
abbrev throughGraph (i : I) := G.induce {a | r a ≤ i}

def inclusion (i : I) (a : Earlier r i) : Through r i := ⟨a.val,le_of_lt a.property⟩

def pairRank : Sym2 V → I :=
  Sym2.lift ⟨fun a b => max (r a) (r b),fun _ _ => max_comm _ _⟩

@[simp] lemma pairRank_mk (a b : V) : pairRank r s(a,b) = max (r a) (r b) := rfl

def triangleConstraint (e f g : Sym2 V) : Prop :=
  ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
    e = s(a,b) ∧ f = s(a,c) ∧ g = s(b,c)

/-- A prescribed coloring of the strict predecessor graph extends literally. -/
def StageExtension (i : I) : Prop :=
  ∀ c : Sym2 (Earlier r i) → ℕ, Valid (earlierGraph G r i) c →
    ∃ d : Sym2 (Through r i) → ℕ, Valid (throughGraph G r i) d ∧
      ∀ a b, d s(inclusion r i a,inclusion r i b) = c s(a,b)

/-- The stage type need not be countable, and no cardinal bound on V is used. -/
theorem cover_of_stage_extensions [WellFoundedLT I] (h : ∀ i, StageExtension G r i) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  apply (Erdos595Work.countable_union_iff_edge_coloring G).mpr
  have hext : ∀ (i : I) (old : Sym2 V → ℕ),
      Erdos595WellOrderedColorExtension.Before (pairRank r) (triangleConstraint G) i old →
      ∃ d, Erdos595WellOrderedColorExtension.Step
        (pairRank r) (triangleConstraint G) i old d := by
    intro i old hold
    let c : Sym2 (Earlier r i) → ℕ := fun e => old (e.map Subtype.val)
    have hc : Valid (earlierGraph G r i) c := by
      intro a b z hab haz hbz hm
      exact hold s(a.val,b.val) s(a.val,z.val) s(b.val,z.val)
        ⟨a.val,b.val,z.val,hab,haz,hbz,rfl,rfl,rfl⟩
        (max_lt a.property b.property) (max_lt a.property z.property)
        (max_lt b.property z.property) hm
    obtain ⟨d,hd,he⟩ := h i c hc
    let d' : Sym2 V → ℕ := Function.extend (Sym2.map (Subtype.val : Through r i → V)) d old
    have hmap : ∀ a b : Through r i, d' s(a.val,b.val) = d s(a,b) := by
      intro a b
      exact (Sym2.map.injective Subtype.val_injective).extend_apply d old s(a,b)
    refine ⟨d',?_,?_⟩
    · rintro e f g ⟨a,b,z,hab,haz,hbz,rfl,rfl,rfl⟩ h₁ h₂ _ hm
      have ha : r a ≤ i := (le_max_left _ _).trans h₁
      have hb : r b ≤ i := (le_max_right _ _).trans h₁
      have hz : r z ≤ i := (le_max_right _ _).trans h₂
      have hh := hd ⟨a,ha⟩ ⟨b,hb⟩ ⟨z,hz⟩ hab haz hbz
      rw [hmap ⟨a,ha⟩ ⟨b,hb⟩,hmap ⟨a,ha⟩ ⟨z,hz⟩,
        hmap ⟨b,hb⟩ ⟨z,hz⟩] at hm
      exact hh hm
    · intro e hri
      induction e using Sym2.inductionOn with
      | hf a b =>
        have ha : r a < i := (le_max_left _ _).trans_lt hri
        have hb : r b < i := (le_max_right _ _).trans_lt hri
        exact (hmap (inclusion r i ⟨a,ha⟩) (inclusion r i ⟨b,hb⟩)).trans
          (he ⟨a,ha⟩ ⟨b,hb⟩)
  obtain ⟨c,hc⟩ := Erdos595WellOrderedColorExtension.global_coloring
    (pairRank r) (triangleConstraint G) hext
  exact ⟨c,fun a b z hab haz hbz => hc _ _ _ ⟨a,b,z,hab,haz,hbz,rfl,rfl,rfl⟩⟩

/-- At an initial stage there are no old pairs to constrain the coloring. -/
theorem initial_stage_extension (i : I) [IsEmpty (Earlier r i)]
    (h : Erdos595Work.IsCountableUnionOfTriangleFree (throughGraph G r i)) :
    StageExtension G r i := by
  intro c _
  obtain ⟨d,hd⟩ := (Erdos595Work.countable_union_iff_edge_coloring _).mp h
  exact ⟨d,hd,fun a => isEmptyElim a⟩

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
  triangleFree : K.CliqueFree 3

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

/-- Finite attachments impose no size or vertex-chromatic restriction on
any of the triangle-free bases. -/
theorem finite_extension (hD : s.D.Finite) : StageExtension G r i := by
  apply s.transfer
  intro c hc
  exact Erdos595UnusedColorAmalgamationExtension.exists_extension_finite
    (earlierGraph G r i) s.K s.D s.embeddings s.distinguished c s.triangleFree hc hD

/-- Infinite attachments are also permitted when the base has a countable
proper vertex coloring. -/
theorem countably_colorable_extension (hK : Nonempty (s.K.Coloring ℕ)) :
    StageExtension G r i := by
  obtain ⟨col⟩ := hK
  apply s.transfer
  intro c hc
  exact Erdos595BipartiteAmalgamationExtension.exists_extension
    (earlierGraph G r i) s.K s.D s.embeddings s.distinguished col c
    s.triangleFree (fun _ _ h => col.valid h) hc

end AmalgamationStage

/-- A continuous well-ordered finite-attachment construction is coverable.
The initial graph may be any coverable graph, not just a triangle-free one. -/
theorem cover_of_finite_amalgamation_stages [WellFoundedLT I]
    (h : ∀ i, (IsEmpty (Earlier r i) ∧
        Erdos595Work.IsCountableUnionOfTriangleFree (throughGraph G r i)) ∨
      ∃ s : AmalgamationStage G r i, s.D.Finite) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  apply cover_of_stage_extensions G r
  intro i
  rcases h i with ⟨hi,hc⟩ | ⟨s,hs⟩
  · letI := hi
    exact initial_stage_extension G r i hc
  · exact s.finite_extension hs

/-- The analogous result for countably vertex-colorable triangle-free bases
has no finiteness requirement on the attaching subgraphs. -/
theorem cover_of_countably_colorable_amalgamation_stages [WellFoundedLT I]
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

#print axioms cover_of_stage_extensions
#print axioms cover_of_finite_amalgamation_stages
#print axioms cover_of_countably_colorable_amalgamation_stages
end Erdos595TransfiniteAmalgamation
