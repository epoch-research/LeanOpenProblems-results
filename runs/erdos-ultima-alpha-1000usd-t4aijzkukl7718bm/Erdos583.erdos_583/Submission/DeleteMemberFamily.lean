import Submission.Work

/-! Removing one indexed trail, with an explicit index map and preserved
supports for the remaining members. Nil removed members are allowed. -/
namespace Erdos583DeleteMemberFamilyDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma exists_delete_member_family {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (T : TrailFamily G (t+1)) (i : Fin (t+1)) (E : Set (Sym2 V))
    (hE : (T.walk i).toSubgraph.edgeSet=E) :
    ∃ U : TrailFamily (G.deleteEdges E) t,
      (∀ j, U.start j=T.start (i.succAbove j)) ∧
      (∀ j, U.finish j=T.finish (i.succAbove j)) ∧
      (∀ j, (U.walk j).support=(T.walk (i.succAbove j)).support) ∧
      (∀ j, (U.walk j).toSubgraph.edgeSet=(T.walk (i.succAbove j)).toSubgraph.edgeSet) := by
  classical
  have hedge (j : Fin t) : ∀ e ∈ (T.walk (i.succAbove j)).edges,
      e ∈ (G.deleteEdges E).edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges]
    refine ⟨(T.walk _).edges_subset_edgeSet he,?_⟩
    intro heE
    rw [←hE] at heE
    exact Set.disjoint_left.mp (T.disjoint (i.succAbove_ne j))
      ((T.walk _).mem_edges_toSubgraph.mpr he) heE
  let p (j : Fin t) := (T.walk (i.succAbove j)).transfer (G.deleteEdges E) (hedge j)
  have hpe (j : Fin t) : (p j).toSubgraph.edgeSet=(T.walk (i.succAbove j)).toSubgraph.edgeSet := by
    ext e
    simp only [p,Walk.mem_edges_toSubgraph,Walk.edges_transfer]
  let U : TrailFamily (G.deleteEdges E) t :=
    { start := fun j ↦ T.start (i.succAbove j)
      finish := fun j ↦ T.finish (i.succAbove j)
      walk := p
      isTrail := fun j ↦ by
        simpa only [p,Walk.isTrail_def,Walk.edges_transfer] using T.isTrail (i.succAbove j)
      disjoint := fun j l hjl ↦ by
        change Disjoint (p j).toSubgraph.edgeSet (p l).toSubgraph.edgeSet
        rw [hpe,hpe]
        exact T.disjoint (fun hh ↦ hjl (i.succAbove_right_injective hh))
      cover := fun e ↦ by
        simp only [hpe,edgeSet_deleteEdges,Set.mem_diff]
        constructor
        · rintro ⟨heG,heE⟩
          obtain ⟨j,hj⟩ := (T.cover e).mp heG
          have hji : j ≠ i := by intro hh; subst j; exact heE (hE ▸ hj)
          obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hji
          exact ⟨l,hj⟩
        · rintro ⟨j,hj⟩
          refine ⟨(T.walk _).toSubgraph.edgeSet_subset hj,?_⟩
          intro heE
          rw [←hE] at heE
          exact Set.disjoint_left.mp (T.disjoint (i.succAbove_ne j)) hj heE }
  exact ⟨U,fun _ ↦ rfl,fun _ ↦ rfl,fun j ↦ by simp only [U,p,Walk.support_transfer],hpe⟩

end Erdos583DeleteMemberFamilyDevelopment
