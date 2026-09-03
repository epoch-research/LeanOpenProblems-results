import Submission.ButterflyPairs
import Submission.PathIntervalReplacement

/-! Two triangles and an intersecting path avoiding their common vertex:
either two paths suffice, or one whole pentagon and one path suffice. -/
namespace Erdos583ButterflyPentagonDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583Work.PathIntervals Erdos583Work.QuotaSurgery
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyPairsDevelopment Erdos583ButterflyContiguousDevelopment
open Erdos583PathIntervalReplacementDevelopment Erdos583ButterflyOrderedAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 4800000
set_option Elab.async false

lemma butterfly_ordered_pentagon {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (f : Fin 5 → V) (hf : Function.Injective f) (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (P : G.Walk a b) (hP : P.IsPath) (hmiss0 : f 0 ∉ P.support)
    (havoid : ∀ i, s(f (baseSource i),f (baseTarget i)) ∉ P.edges)
    (p : Fin 4 → Fin 4) (hpi : Function.Injective p) (h : Fin 4 → ℕ) (hh : StrictMono h)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=f (outer (p i)))
    (hstep : ∀ i : Fin 3, h i.succ=h i.castSucc+1) :
    ∃ C : G.Walk (f 0) (f 0), ∃ Q : G.Walk a b,
      C.IsCycle ∧ C.length=5 ∧ Q.IsPath ∧ Disjoint C.toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      C.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet := by
  classical
  have h01 : h 1=h 0+1 := hstep 0
  have h12 : h 2=h 1+1 := hstep 1
  have h23 : h 3=h 2+1 := hstep 2
  have h03 : h 0 ≤ h 3 := hh.monotone (by decide)
  have hadj (i : Fin 3) : G.Adj (f (outer (p i.castSucc))) (f (outer (p i.succ))) := by
    have hlt : h i.castSucc < P.length := (hh (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).trans_le (hb i.succ)
    have hh' := P.adj_getVert_succ hlt
    rwa [←hstep i,hc i.castSucc,hc i.succ] at hh'
  have hemem (i : Fin 3) : s(f (outer (p i.castSucc)),f (outer (p i.succ))) ∈ P.edges := by
    apply (edges_positions P _).mpr
    refine ⟨h i.castSucc,(hh (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).trans_le (hb i.succ),?_⟩
    rw [←hstep i,hc i.castSucc,hc i.succ]
  have hnpaired (i : Fin 3) : ¬paired (p i.castSucc) (p i.succ) := by
    rintro ⟨e,he⟩
    have hmap := congrArg (Sym2.map f) he
    simp only [Sym2.map_mk] at hmap
    exact havoid e (hmap.symm ▸ hemem i)
  have hpN : [p 0,p 1,p 2,p 3].Nodup := by
    simpa only [List.ofFn_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] using List.nodup_ofFn.mpr hpi
  obtain ⟨huw,hvz⟩ := opposite_pairs_vec (p 0) (p 1) (p 2) (p 3) hpN (hnpaired 0) (hnpaired 1) (hnpaired 2)
  have hadj01 : G.Adj (f (outer (p 0))) (f (outer (p 1))) := hadj 0
  have hadj12 : G.Adj (f (outer (p 1))) (f (outer (p 2))) := hadj 1
  have hadj23 : G.Adj (f (outer (p 2))) (f (outer (p 3))) := hadj 2
  let C : G.Walk (f 0) (f 0) := Walk.cons (hub_adj f ha (p 0))
    (Walk.cons (paired_adj f ha huw) (Walk.cons hadj12.symm
      (Walk.cons (paired_adj f ha hvz) (Walk.cons (hub_adj f ha (p 3)).symm Walk.nil))))
  let R : G.Walk (f (outer (p 0))) (f (outer (p 3))) := Walk.cons hadj01
    (Walk.cons (hub_adj f ha (p 1)).symm (Walk.cons (hub_adj f ha (p 2)) (Walk.cons hadj23 Walk.nil)))
  have hroot (i : Fin 4) : f 0 ≠ f (outer (p i)) := by
    intro he
    have hv := congrArg Fin.val (hf he)
    dsimp [outer] at hv
    omega
  have hne (i j : Fin 4) (hij : i ≠ j) : f (outer (p i)) ≠ f (outer (p j)) :=
    (hf.comp (outer_injective.comp hpi)).ne hij
  have hroot' (i : Fin 4) : f (outer (p i)) ≠ f 0 := (hroot i).symm
  have hC : C.IsCycle := by
    simp [C,Walk.cons_isCycle_iff,Walk.isPath_def,hroot,hroot',hne]
  have hR : R.IsPath := by
    apply Walk.IsPath.mk'
    simp [R,Walk.support,hroot,hroot',hne]
  let M := interval P (h 0) (h 3) h03
  have hMe : M.toSubgraph.edgeSet=
      {s(f (outer (p 0)),f (outer (p 1))),s(f (outer (p 1)),f (outer (p 2))),s(f (outer (p 2)),f (outer (p 3)))} := by
    ext e
    rw [show M.toSubgraph.edgeSet=(interval P (h 0) (h 3) h03).toSubgraph.edgeSet from rfl,
      interval_edges P h03 (hb 3)]
    constructor
    · rintro ⟨i,h0i,hi3,hei⟩
      have hi : i=h 0 ∨ i=h 1 ∨ i=h 2 := by omega
      rcases hi with rfl | rfl | rfl
      · exact Or.inl (by simpa only [←h01,hc 0,hc 1] using hei)
      · exact Or.inr (Or.inl (by simpa only [←h12,hc 1,hc 2] using hei))
      · exact Or.inr (Or.inr (by simpa only [←h23,hc 2,hc 3] using hei))
    · rintro (rfl|rfl|rfl)
      · exact ⟨h 0,le_rfl,by omega,by rw [←h01,hc 0,hc 1]⟩
      · exact ⟨h 1,by omega,by omega,by rw [←h12,hc 1,hc 2]⟩
      · exact ⟨h 2,by omega,by omega,by rw [←h23,hc 2,hc 3]⟩
  have hlocal : C.toSubgraph.edgeSet ∪ R.toSubgraph.edgeSet=coreEdges baseSource baseTarget f ∪ M.toSubgraph.edgeSet := by
    rw [mapped_core_relabel f hpN (hnpaired 0) (hnpaired 1) (hnpaired 2),hMe]
    ext e
    simp only [C,R,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,
      or_false,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap]
    tauto
  have hcoreold (u : Fin 5) (hu : f u ∈ P.support) : f u ∈ M.support := by
    have hu0 : u ≠ 0 := fun he ↦ hmiss0 (he ▸ hu)
    obtain ⟨i,hi⟩ := outer_surjective_away_zero p hpi hu0
    exact (interval_support P h03 (hb 3) _).mpr ⟨h i,hh.monotone (Fin.zero_le _),hh.monotone (Fin.le_last _),
      (congrArg f hi).symm.trans (hc i).symm⟩
  let R' := R.copy (hc 0).symm (hc 3).symm
  have hR'e : R'.toSubgraph=R.toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hR'old : ∀ x ∈ R'.support, x ∈ P.support → x ∈ M.support := by
    intro x hx hxP
    simp only [R',Walk.support_copy,R,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact hcoreold _ hxP
  let Q := (P.take (h 0)).append (R'.append (P.drop (h 3)))
  have hQ : Q.IsPath := replace_interval_isPath P hP h03 (hb 3) R' (by simpa only [R',Walk.isPath_copy] using hR) hR'old
  have hcover : C.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet := by
    have hPe := congrArg (fun W ↦ W.toSubgraph.edgeSet) (split_interval P h03 (hb 3))
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hPe
    ext e
    have hl := congrArg (fun S : Set (Sym2 V) ↦ e ∈ S) hlocal
    have hp' := congrArg (fun S : Set (Sym2 V) ↦ e ∈ S) hPe
    simp only [Q,Walk.toSubgraph_append,Subgraph.edgeSet_sup,hR'e,Set.mem_union] at hl hp' ⊢
    change (e ∈ C.toSubgraph.edgeSet ∨ e ∈ (P.take (h 0)).toSubgraph.edgeSet ∨
      e ∈ R.toSubgraph.edgeSet ∨ e ∈ (P.drop (h 3)).toSubgraph.edgeSet) ↔
      e ∈ coreEdges baseSource baseTarget f ∨ e ∈ P.toSubgraph.edgeSet
    change (e ∈ P.toSubgraph.edgeSet) =
      (e ∈ (P.take (h 0)).toSubgraph.edgeSet ∨ e ∈ M.toSubgraph.edgeSet ∨ e ∈ (P.drop (h 3)).toSubgraph.edgeSet) at hp'
    tauto
  have hKc : (coreEdges baseSource baseTarget f).ncard=6 := by
    rw [coreEdges,Set.iUnion_singleton_eq_range,
      Set.ncard_range_of_injective (mapped_core_edge_injective _ _ base_edge_injective f hf)]
    simp
  have hdK : Disjoint (coreEdges baseSource baseTarget f) P.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he heP
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    have hi' : e=s(f (baseSource i),f (baseTarget i)) := hi
    subst e
    exact havoid i (P.mem_edges_toSubgraph.mp heP)
  have hlen : C.length+Q.length=(coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet).ncard := by
    rw [Set.ncard_union_eq hdK,hKc,trail_edgeSet_ncard P hP.isTrail]
    simp only [C,Q,R',R,Walk.length_cons,Walk.length_nil,Walk.length_append,Walk.length_copy,
      Walk.take_length,Walk.drop_length,inf_eq_left.mpr (hb 0)]
    have hlast := hb 3
    omega
  exact ⟨C,Q,hC,rfl,hQ,disjoint_of_cover_length C Q hC.isTrail hQ.isTrail _ hcover hlen,hcover⟩

lemma butterfly_path_or_pentagon {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (f : Fin 5 → V) (hf : Function.Injective f) (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (P : G.Walk a b) (hP : P.IsPath) (hmiss0 : f 0 ∉ P.support)
    (htouch : ∃ i, f i ∈ P.support)
    (havoid : ∀ i, s(f (baseSource i),f (baseTarget i)) ∉ P.edges) :
    TwoPathCover (G := G) (coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet) ∨
      ∃ C : G.Walk (f 0) (f 0), ∃ Q : G.Walk a b,
        C.IsCycle ∧ C.length=5 ∧ Q.IsPath ∧ Disjoint C.toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
        C.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet := by
  classical
  by_cases hno : TwoPathCover (G := G) (coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet)
  · exact Or.inl hno
  obtain ⟨p,h,hpi,hh,hb,hc,hstep⟩ := butterfly_nonabsorbable_contiguous f hf ha P hP hmiss0 htouch havoid hno
  exact Or.inr (butterfly_ordered_pentagon f hf ha P hP hmiss0 havoid p hpi h hh hb hc hstep)

end Erdos583ButterflyPentagonDevelopment
