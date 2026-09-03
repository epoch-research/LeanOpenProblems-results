import Submission.JoinCycleAbsorption

/-! Absorb a touching path while retaining a specified class of complementary core edge sets. -/
namespace Erdos583ComplementCycleResidueDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583JoinCycleAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma cycle_residue_absorption {V W : Type*} [Fintype V]
    {G : SimpleGraph V} {a b : V} (H : SimpleGraph W) (f : W → V)
    (hdisc : ¬Hᶜ.Preconnected) (R : Set (Sym2 V) → Prop)
    (hparts : ∀ x y, H.Adj x y → ∃ r, ∃ C : G.Walk r r,
      C.IsCycle ∧ C.toSubgraph.verts ⊆ Set.range f ∧
      C.toSubgraph.Adj (f x) (f y) ∧
      C.toSubgraph.edgeSet ⊆ Sym2.map f '' H.edgeSet ∧
      R ((Sym2.map f '' H.edgeSet) \ C.toSubgraph.edgeSet))
    (P : G.Walk a b) (hp : P.IsPath)
    (hd : Disjoint (Sym2.map f '' H.edgeSet) P.toSubgraph.edgeSet)
    (hhit : ∃ v, v ∈ P.support ∧ v ∈ Set.range f) :
    ∃ E F : Set (Sym2 V), R E ∧ TwoPathCover (G := G) F ∧
      Disjoint E F ∧ E ∪ F=(Sym2.map f '' H.edgeSet) ∪ P.toSubgraph.edgeSet := by
  classical
  let I := {p : W × W // H.Adj p.1 p.2}
  have hdata (i : I) := hparts i.val.1 i.val.2 i.property
  choose r C hC hCS he hsub hR using hdata
  obtain ⟨i,hi⟩ := cycles_absorb_of_disconnected_complement H f hdisc r C hC hCS
    (fun x y hxy ↦ ⟨⟨(x,y),hxy⟩,he ⟨(x,y),hxy⟩⟩) P hp
    (fun i ↦ hd.mono_left (hsub i)) hhit
  refine ⟨(Sym2.map f '' H.edgeSet) \ (C i).toSubgraph.edgeSet,
    (C i).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet,hR i,hi,?_,?_⟩
  · apply disjoint_sup_right.mpr
    constructor
    · exact Set.disjoint_left.mpr (fun _ hq hc ↦ hq.2 hc)
    · exact hd.mono_left Set.diff_subset
  · rw [←Set.union_assoc,Set.diff_union_of_subset (hsub i)]

end Erdos583ComplementCycleResidueDevelopment
