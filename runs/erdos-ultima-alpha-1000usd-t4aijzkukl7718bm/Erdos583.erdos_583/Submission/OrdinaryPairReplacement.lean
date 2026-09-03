import Submission.ShortTriangleQuarticExclusion

/-! Replace two ordinary path members while retaining the rooted defect exactly. -/
namespace Erdos583OrdinaryPairReplacementDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma replace_two_paths_preserving_root {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (i j : Fin k) (hij : i ≠ j)
    (hiL : i ≠ L.index) (hjL : j ≠ L.index) {a b c d : V}
    (P : G.Walk a b) (Q : G.Walk c d) (hP : P.IsPath) (hQ : Q.IsPath)
    (hd : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet)
    (he : P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧ M.tail.length=L.tail.length ∧
      (U.walk i).toSubgraph=P.toSubgraph ∧ (U.walk j).toSubgraph=Q.toSubgraph := by
  obtain ⟨A,hAi,hAj,hAl,hAs⟩ := GeneralPair.replace_two T i j hij a b c d P Q
    hP.isTrail hQ.isTrail hd he
  have hpold := (T.one_defect_other_paths hs L.index L.member_not_path).2 i hiL
  have hqold := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hjL
  have hsum := congrArg Set.ncard he
  rw [Set.ncard_union_eq hd,Set.ncard_union_eq (T.disjoint hij),
    trail_edgeSet_ncard _ hP.isTrail,trail_edgeSet_ncard _ hQ.isTrail,
    trail_edgeSet_ncard _ (T.isTrail i),trail_edgeSet_ncard _ (T.isTrail j)] at hsum
  rw [(walk_vertex_ncard_eq_iff _).mpr hpold,(walk_vertex_ncard_eq_iff _).mpr hqold,
    (walk_vertex_ncard_eq_iff _).mpr hP,(walk_vertex_ncard_eq_iff _).mpr hQ] at hAs
  have hscore : A.score=T.score := by omega
  have hCS := trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
    (edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter)
  have hAL : (A.walk L.index).toSubgraph=(L.cycle.append L.tail).toSubgraph :=
    (hAl L.index hiL.symm hjL.symm).trans L.subgraph
  obtain ⟨U,hUs,hUa,hUb,hparts,_⟩ := replace_one_general A L.index (L.cycle.append L.tail) hCS hAL.symm
  let M : RootedCycleRep U r :=
    ⟨L.index,L.finish,hUa,hUb,L.cycle,L.tail,L.isCycle,L.isPath,L.inter,(hparts L.index).trans hAL⟩
  exact ⟨U,M,hUs.trans hscore,rfl,rfl,(hparts i).trans hAi,(hparts j).trans hAj⟩

end Erdos583OrdinaryPairReplacementDevelopment
