import Submission.TriangleOneTailDegreeSeven

/-! Replace one rooted cycle-and-tail member and one ordinary path, retaining the new rooted witness. -/
namespace Erdos583RootedPairReplacementDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma replace_rooted_pair {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (j : Fin k) (hij : L.index ≠ j)
    {t a b : V} (C : G.Walk r r) (S : G.Walk r t) (Q : G.Walk a b)
    (hC : C.IsCycle) (hS : S.IsPath) (hQ : Q.IsPath)
    (hint : ∀ z ∈ C.support, z ∈ S.support → z=r)
    (hd : Disjoint (C.append S).toSubgraph.edgeSet Q.toSubgraph.edgeSet)
    (he : (C.append S).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
      (T.walk L.index).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=C ∧ M.tail.length=S.length := by
  have hX := trail_append_of_disjoint hC.isTrail hS.isTrail
    (edge_disjoint_of_one_common_vertex C S hint)
  obtain ⟨A,hAi,_,_,hAs⟩ := GeneralPair.replace_two T L.index j hij r t a b
    (C.append S) Q hX hQ.isTrail hd he
  have hold := trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
    (edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter)
  have hOldLen : (T.walk L.index).length=(L.cycle.append L.tail).length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail L.index),L.subgraph,trail_edgeSet_ncard _ hold]
  have hOldCard : (T.walk L.index).toSubgraph.verts.ncard=(T.walk L.index).length := by
    rw [L.subgraph,lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,hOldLen]
  have hXCard := lollipop_vertex_card C hC S hS hint
  have hOldP := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hsum := congrArg Set.ncard he
  rw [Set.ncard_union_eq hd,Set.ncard_union_eq (T.disjoint hij),trail_edgeSet_ncard _ hX,
    trail_edgeSet_ncard _ hQ.isTrail,trail_edgeSet_ncard _ (T.isTrail L.index),
    trail_edgeSet_ncard _ (T.isTrail j)] at hsum
  rw [hOldCard,hXCard,(walk_vertex_ncard_eq_iff _).mpr hOldP,
    (walk_vertex_ncard_eq_iff _).mpr hQ] at hAs
  have hscore : A.score=T.score := by omega
  obtain ⟨U,hUs,hUa,hUb,hparts,_⟩ := replace_one_general A L.index (C.append S) hX hAi.symm
  let M : RootedCycleRep U r :=
    ⟨L.index,t,hUa,hUb,C,S,hC,hS,hint,(hparts L.index).trans hAi⟩
  exact ⟨U,M,hUs.trans hscore,rfl,rfl⟩

end Erdos583RootedPairReplacementDevelopment
