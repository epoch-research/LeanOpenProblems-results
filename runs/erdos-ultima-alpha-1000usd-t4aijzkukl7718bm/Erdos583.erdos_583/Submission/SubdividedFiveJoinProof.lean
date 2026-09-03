import Submission.ComplementCycleResidue
import Submission.SubdividedFiveCycles

/-! The subdivided-K5 absorption follows from the general disconnected-complement criterion. -/
namespace Erdos583SubdividedFiveJoinProofDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583SubdividedFiveFiniteDevelopment Erdos583SubdividedFiveCyclesDevelopment
open Erdos583ComplementCycleResidueDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma base_complement_not_preconnected : ¬baseᶜ.Preconnected := by
  decide

lemma subdivided_five_join_path_to_pentagon {V : Type*} [Fintype V] {G : SimpleGraph V}
    (f : base →g G) (hf : Function.Injective f) {a b : V} (P : G.Walk a b) (hP : P.IsPath)
    (hd : Disjoint (Sym2.map f '' base.edgeSet) P.toSubgraph.edgeSet)
    (htouch : ∃ u : Fin 6, f u ∈ P.support) :
    ∃ C : G.Walk (f 0) (f 0), C.IsCycle ∧ C.length=5 ∧
      ∃ E : Set (Sym2 V), Disjoint C.toSubgraph.edgeSet E ∧
        C.toSubgraph.edgeSet ∪ E=(Sym2.map f '' base.edgeSet) ∪ P.toSubgraph.edgeSet ∧
        TwoPathCover (G := G) E := by
  let R (E : Set (Sym2 V)) : Prop :=
    ∃ C : G.Walk (f 0) (f 0), C.IsCycle ∧ C.length=5 ∧ C.toSubgraph.edgeSet=E
  have hparts (x y : Fin 6) (hxy : base.Adj x y) :
      ∃ r, ∃ C : G.Walk r r, C.IsCycle ∧ C.toSubgraph.verts ⊆ Set.range f ∧
        C.toSubgraph.Adj (f x) (f y) ∧
        C.toSubgraph.edgeSet ⊆ Sym2.map f '' base.edgeSet ∧
        R ((Sym2.map f '' base.edgeSet) \ C.toSubgraph.edgeSet) := by
    obtain ⟨C,D,hC,hCl,hD,hDs,he,hCD,hcov⟩ := mapped_cycle_choice f hf hxy
    refine ⟨f 0,D,hD,?_,he,?_,C,hC,hCl,?_⟩
    · intro z hz
      exact (hDs z).mp (D.mem_verts_toSubgraph.mp hz)
    · intro e he
      rw [←hcov]
      exact Or.inr he
    · rw [←hcov]
      ext e
      constructor
      · intro he
        exact ⟨Or.inl he,fun hh ↦ Set.disjoint_left.mp hCD he hh⟩
      · rintro ⟨hc|hd,hn⟩
        · exact hc
        · exact (hn hd).elim
  obtain ⟨E,F,⟨C,hC,hCl,hCE⟩,hF,hEF,hcov⟩ := cycle_residue_absorption base f
    base_complement_not_preconnected R hparts P hP hd (by
      obtain ⟨u,hu⟩ := htouch
      exact ⟨f u,hu,⟨u,rfl⟩⟩)
  exact ⟨C,hC,hCl,F,hCE.symm ▸ hEF,by rw [hCE]; exact hcov,hF⟩

end Erdos583SubdividedFiveJoinProofDevelopment
