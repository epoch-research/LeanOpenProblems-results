import Submission.CycleFirstVisitRotation

/-! Whole-cycle exclusion for unrestricted shortest rooted cycles. -/
namespace Erdos583FreeRootWholeCycleExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar
open Erdos583FreeRootCycleMinimumDevelopment Erdos583CycleFirstVisitRotationDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma minimum_whole_cycle_other_path_disjoint {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmin : ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
      W.score=T.score → C.length ≤ M.cycle.length)
    (hp : (T.walk j).IsPath) :
    Disjoint (T.walk j).toSubgraph.verts C.toSubgraph.verts := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxP hxC
  obtain ⟨u,hu,A,D,hP,hA⟩ := QuadrilateralAbsorption.first_hit_split (T.walk j)
    C.toSubgraph.verts ⟨x,(T.walk j).mem_verts_toSubgraph.mp hxP,hxC⟩
  have huC := C.mem_verts_toSubgraph.mp hu
  let E := C.rotate huC
  have hE : E.IsCycle := hC.rotate huC
  have hEC : E.toSubgraph=C.toSubgraph := C.toSubgraph_rotate huC
  obtain ⟨v,h,Q,hcycle,hsub⟩ : ∃ v, ∃ h : G.Adj u v, ∃ Q : G.Walk v u,
      (Walk.cons h Q).IsCycle ∧ (Walk.cons h Q).toSubgraph=C.toSubgraph := by
    cases he : E with
    | nil => exact (hE.not_nil (he ▸ Walk.Nil.nil)).elim
    | cons h Q => exact ⟨_,h,Q,he ▸ hE,he ▸ hEC⟩
  have huv : C.toSubgraph.Adj u v := by
    rw [←hsub]
    simpa only [Walk.snd_cons] using (Walk.cons h Q).toSubgraph_adj_snd (by simp)
  have hvD := CycleFirstVisits.maximal_first_visit_neighbors_present T hm i j hij C hC hi hp
    A D hP (fun z hz hc ↦ hA z hz (C.mem_verts_toSubgraph.mpr hc)) huv
  obtain ⟨w,R,f,hR⟩ := TerminalTail.nonnil_last_edge (D.takeUntil v hvD)
    (Walk.not_nil_of_ne h.ne)
  let B := D.dropUntil v hvD
  have hD : D=R.append (Walk.cons f B) := by
    calc
      D=(D.takeUntil v hvD).append B := (Walk.take_spec D hvD).symm
      _=(R.concat f).append B := by rw [hR]
      _=R.append (Walk.cons f B) := by
        rw [Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
  have hform : T.walk j=A.append (R.append (Walk.cons f B)) := by rw [hP,hD]
  obtain ⟨U,M,hUs,hshort⟩ := maximum_cycle_first_visit_shortening T hm i j hij h Q hcycle
    (hi.trans hsub.symm) A R f B (hform ▸ hp)
    (fun z hzA hzC ↦ hA z hzA (hsub ▸ (Walk.cons h Q).mem_verts_toSubgraph.mpr hzC))
    (congrArg Walk.toSubgraph hform)
  have hlen : (Walk.cons h Q).length=C.length := by
    rw [←trail_edgeSet_ncard _ hcycle.isTrail,hsub,trail_edgeSet_ncard C hC.isTrail]
  have hh := hmin U w M hUs
  omega

lemma minimum_whole_cycle_impossible {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : G.Connected) {k : ℕ} (hk : 2 ≤ k) (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmin : ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
      W.score=T.score → C.length ≤ M.cycle.length)
    (hp : ∀ j, j ≠ i → (T.walk j).IsPath) : False := by
  classical
  have hd (j : Fin k) (hji : j ≠ i) :
      Disjoint (T.walk j).toSubgraph.verts C.toSubgraph.verts :=
    minimum_whole_cycle_other_path_disjoint T hm i j hji.symm C hC hi hmin (hp j hji)
  have hclosed : C.toSubgraph.verts=Set.univ := TrailBudget.connected_closed_set hG
    C.toSubgraph.verts ⟨r,C.start_mem_verts_toSubgraph⟩ (by
      intro x y hxy hx
      obtain ⟨j,hj⟩ := (T.cover s(x,y)).mp hxy
      by_cases hji : j=i
      · subst j
        rw [hi] at hj
        exact C.toSubgraph.edge_vert (Subgraph.adj_symm C.toSubgraph hj)
      · exact (Set.disjoint_left.mp (hd j hji) ((T.walk j).toSubgraph.edge_vert hj) hx).elim)
  let j : Fin k := if i.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hji : j ≠ i := by
    intro he
    have he' := congrArg Fin.val he
    dsimp only [j] at he'
    split_ifs at he' <;> simp_all
  have hjC : T.start j ∈ C.toSubgraph.verts := by rw [hclosed]; trivial
  exact Set.disjoint_left.mp (hd j hji) (T.walk j).start_mem_verts_toSubgraph hjC

lemma unrestricted_minimum_tail_not_nil {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : G.Connected) {k : ℕ} (hk : 2 ≤ k) (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
      W.score=T.score → L.cycle.length ≤ M.cycle.length) : ¬L.tail.Nil := by
  intro hn
  have hi : (T.walk L.index).toSubgraph=L.cycle.toSubgraph := by
    have hnil {a b c : V} (P : G.Walk a b) (Q : G.Walk b c) (hQ : Q.Nil) :
        (P.append Q).toSubgraph=P.toSubgraph := by cases hQ; simp
    rw [L.subgraph,hnil L.cycle L.tail hn]
  exact minimum_whole_cycle_impossible hG hk T hm L.index L.cycle L.isCycle hi hmin
    (T.one_defect_other_paths hs L.index L.member_not_path).2

end Erdos583FreeRootWholeCycleExclusionDevelopment
