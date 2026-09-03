import Submission.EndpointUnpairing

/-! Separation of a single adjacent endpoint pair in an all-odd path system,
provided the pair is not an isolated edge. -/
namespace Erdos583AdjacentEndpointUnpairingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.NormalTrailSystem Erdos583Work.TrailNormalization
open Erdos583Work.RootedTailSystem Erdos583Work.SingletonRotation
open Erdos583Work.InducedBuffer
open Erdos583EndpointUnpairingDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

lemma all_paths_maximum (T : NormalTrailSystem G k) (hp : ∀ i, (T.walk i).IsPath) :
    ∀ U : NormalTrailSystem G k, U.score ≤ T.score := by
  intro U
  rw [T.score_eq_edges_add_iff.mpr hp]
  exact U.score_le_edges_add

lemma singleton_unpair_split (T : NormalTrailSystem G k)
    (hp : ∀ i, (T.walk i).IsPath) (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.finish i))
    (hi : (T.walk i).toSubgraph=G.subgraphOfAdj h)
    (A : G.Walk (T.start j) (T.start i)) (B : G.Walk (T.start i) (T.finish j))
    (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hav : T.finish i ∉ A.support) :
    ∃ U : NormalTrailSystem G k, (∀ l, (U.walk l).IsPath) ∧
      U.score=T.score ∧ owner U (T.start i) ≠ owner U (T.finish i) := by
  have hbuf : (A.append (Walk.cons h Walk.nil)).IsPath := by
    rw [←Walk.concat_eq_append]
    exact hAB.of_append_left.concat hav h
  obtain ⟨U,hle,hUj,hUi,hUja,_⟩ := move_stem_to_singleton T j i hij.symm h hi
    A B hAB.isTrail hj hbuf
  have hs : U.score=T.score := le_antisymm (all_paths_maximum T hp U) hle
  have hUp : ∀ l, (U.walk l).IsPath := U.score_eq_edges_add_iff.mp
    (hs.trans (T.score_eq_edges_add_iff.mpr hp))
  have ha : owner U (T.start i)=j := (endpoint_iff_owner U _ _).mp (Or.inl hUja.symm)
  have hb : owner U (T.finish i)=i := (endpoint_iff_owner U _ _).mp
    (endpoints_of_path_subgraph U i (A.append (Walk.cons h Walk.nil)) hbuf
      (by simp [Walk.nil_append_iff]) hUi).2
  exact ⟨U,hUp,hs,by rw [ha,hb]; exact hij.symm⟩

lemma singleton_unpair_carrier (T : NormalTrailSystem G k)
    (hp : ∀ i, (T.walk i).IsPath) (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.finish i))
    (hi : (T.walk i).toSubgraph=G.subgraphOfAdj h)
    (ha : T.start i ∈ (T.walk j).support) :
    ∃ U : NormalTrailSystem G k, (∀ l, (U.walk l).IsPath) ∧
      U.score=T.score ∧ owner U (T.start i) ≠ owner U (T.finish i) := by
  classical
  let A := (T.walk j).takeUntil (T.start i) ha
  let B := (T.walk j).dropUntil (T.start i) ha
  have hAB : A.append B=T.walk j := Walk.take_spec _ ha
  by_cases hav : T.finish i ∉ A.support
  · exact singleton_unpair_split T hp i j hij h hi A B (hAB ▸ hp j)
      (congrArg Walk.toSubgraph hAB).symm hav
  have hbB : T.finish i ∉ B.support := by
    intro hb
    have hx : T.finish i=T.start i := by
      by_contra hn
      exact ((hAB ▸ hp j).ne_of_mem_support_of_append hn (not_not.mp hav) hb) rfl
    exact (T.endpoints_ne i) hx.symm
  obtain ⟨R,hRs,hR⟩ := T.orient (fun l ↦ decide (l=j))
  have hRia : R.start i=T.start i := by simpa [hij] using (hR i).1
  have hRib : R.finish i=T.finish i := by simpa [hij] using (hR i).2.1
  have hRja : R.start j=T.finish j := by simpa using (hR j).1
  have hRjb : R.finish j=T.start j := by simpa using (hR j).2.1
  have hRp : ∀ l, (R.walk l).IsPath := R.score_eq_edges_add_iff.mp
    (hRs.trans (T.score_eq_edges_add_iff.mpr hp))
  let A' := B.reverse.copy hRja.symm hRia.symm
  let B' := A.reverse.copy hRia.symm hRjb.symm
  have he : (A'.append B').toSubgraph=(T.walk j).toSubgraph := by
    simp only [A',B',Walk.append_copy_copy,NormalTrailSystem.walk_copy_subgraph]
    rw [←Walk.reverse_append,hAB,Walk.toSubgraph_reverse]
  have hp' : (A'.append B').IsPath := by
    simp only [A',B',Walk.append_copy_copy,Walk.isPath_copy]
    rw [←Walk.reverse_append,hAB]
    exact (hp j).reverse
  have hav' : R.finish i ∉ A'.support := by
    simpa only [A',Walk.support_copy,Walk.support_reverse,List.mem_reverse,hRib] using hbB
  have h' : G.Adj (R.start i) (R.finish i) := by rw [hRia,hRib]; exact h
  have hi' : (R.walk i).toSubgraph=G.subgraphOfAdj h' := by
    rw [(hR i).2.2,hi]
    ext <;> simp [hRia,hRib]
  obtain ⟨U,hUp,hUs,hU⟩ := singleton_unpair_split R hRp i j hij h' hi' A' B' hp'
    ((hR j).2.2.trans he.symm) hav'
  exact ⟨U,hUp,hUs.trans hRs,by simpa only [hRia,hRib] using hU⟩

lemma separate_adjacent_endpoints_of_neighbor (T : NormalTrailSystem G k)
    (hp : ∀ i, (T.walk i).IsPath) {a b x : V}
    (hab : G.Adj a b) (hax : G.Adj a x) (hxb : x ≠ b) :
    ∃ U : NormalTrailSystem G k, (∀ i, (U.walk i).IsPath) ∧
      U.score=T.score ∧ owner U a ≠ owner U b := by
  classical
  obtain ⟨S,hSs,t,Q,hQ,hmem⟩ := force_first_edge T (all_paths_maximum T hp) hab
  have hSp : ∀ i, (S.walk i).IsPath := S.score_eq_edges_add_iff.mp
    (hSs.trans (T.score_eq_edges_add_iff.mpr hp))
  have hpath := max_score_member_isPath S (all_paths_maximum S hSp) _ hQ hmem
  obtain ⟨i,hends,hi⟩ := hmem
  have ha : owner S a=i := (endpoint_iff_owner S _ i).mp (hends.elim
    (fun hh ↦ Or.inl hh.1.symm) (fun hh ↦ Or.inr hh.2.symm))
  by_cases hqt : Q.Nil
  · cases hqt
    have hb : b=S.start i ∨ b=S.finish i := hends.elim
      (fun hh ↦ Or.inr hh.2.symm) (fun hh ↦ Or.inl hh.1.symm)
    obtain ⟨R,hRs,hRa,hRest,hRe⟩ := orient_receiver S i a ((endpoint_iff_owner S a i).mpr ha)
    have hRb : R.finish i=b := by
      have hb' := (endpoints_of_path_subgraph R i (Walk.cons hab Walk.nil) hpath
        (by simp) ((hRe i).trans hi)).2
      exact (hb'.resolve_left (by rw [hRa]; exact hab.ne.symm)).symm
    have hRp : ∀ l, (R.walk l).IsPath := R.score_eq_edges_add_iff.mp
      (hRs.trans (S.score_eq_edges_add_iff.mpr hSp))
    have h : G.Adj (R.start i) (R.finish i) := by rw [hRa,hRb]; exact hab
    have hRi : (R.walk i).toSubgraph=G.subgraphOfAdj h := by
      rw [hRe,hi,Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
      ext <;> simp [hRa,hRb]
    obtain ⟨j,hj⟩ := (R.cover s(a,x)).mp hax
    have hij : i ≠ j := by
      intro he
      subst j
      rw [hRi] at hj
      have hh : (R.start i=a ∧ R.finish i=x) ∨ (R.start i=x ∧ R.finish i=a) := by
        simpa only [edgeSet_subgraphOfAdj,Set.mem_singleton_iff,Sym2.eq_iff,eq_comm,and_comm] using hj
      rcases hh with hh|hh
      · exact hxb (hh.2.symm.trans hRb)
      · exact hax.ne (hRa.symm.trans hh.1)
    have hroot : R.start i ∈ (R.walk j).support := by
      rw [hRa]
      exact (R.walk j).fst_mem_support_of_mem_edges ((R.walk j).mem_edges_toSubgraph.mp hj)
    obtain ⟨U,hUp,hUs,hU⟩ := singleton_unpair_carrier R hRp i j hij h hRi hroot
    exact ⟨U,hUp,hUs.trans (hRs.trans hSs),by simpa only [hRa,hRb] using hU⟩
  · refine ⟨S,hSp,hSs,?_⟩
    intro hown
    have hb := (endpoint_iff_owner S b i).mpr (hown.symm.trans ha)
    have ht : b=t := by
      rcases hends with hh|hh
      · rw [hh.1,hh.2] at hb
        exact hb.resolve_left hab.ne.symm
      · rw [hh.1,hh.2] at hb
        exact hb.resolve_right hab.ne.symm
    have hnil : Q.Nil := by
      subst t
      rw [(Walk.isPath_iff_eq_nil Q).mp hpath.of_cons]
      exact Walk.Nil.nil
    exact hqt hnil

omit [Fintype V] in
lemma connected_edge_has_other_neighbor (hG : G.Connected) {a b : V}
    (hab : G.Adj a b) (hmore : ∃ c : V, c ≠ a ∧ c ≠ b) :
    (∃ x, G.Adj a x ∧ x ≠ b) ∨ (∃ x, G.Adj b x ∧ x ≠ a) := by
  by_contra hn
  have hclosed : ({a,b} : Set V)=Set.univ := TrailBudget.connected_closed_set hG
    ({a,b} : Set V) ⟨a,Or.inl rfl⟩ (by
      intro x y hxy hx
      rcases hx with rfl|rfl
      · exact Or.inr (by by_contra hy; exact hn (Or.inl ⟨y,hxy,hy⟩))
      · exact Or.inl (by by_contra hy; exact hn (Or.inr ⟨y,hxy,hy⟩)))
  obtain ⟨c,hca,hcb⟩ := hmore
  have hc : c ∈ ({a,b} : Set V) := hclosed.symm ▸ Set.mem_univ c
  exact hc.elim hca hcb

lemma separate_distinct_endpoints (T : NormalTrailSystem G k)
    (hp : ∀ i, (T.walk i).IsPath) (hG : G.Connected)
    (hcard : 2 < Fintype.card V) (a b : V) (hab : a ≠ b) :
    ∃ U : NormalTrailSystem G k, (∀ i, (U.walk i).IsPath) ∧
      U.score=T.score ∧ owner U a ≠ owner U b := by
  by_cases hadj : G.Adj a b
  · have hmore : ∃ c : V, c ≠ a ∧ c ≠ b := by
      by_contra hn
      have he : (Set.univ : Set V) ⊆ {a,b} := by
        intro c _
        by_contra hc
        exact hn ⟨c,fun h ↦ hc (Or.inl h),fun h ↦ hc (Or.inr h)⟩
      have hh := Set.ncard_le_ncard he
      rw [Set.ncard_univ,Nat.card_eq_fintype_card,Set.ncard_pair hab] at hh
      omega
    rcases connected_edge_has_other_neighbor hG hadj hmore with ⟨x,hax,hxb⟩|⟨x,hbx,hxa⟩
    · exact separate_adjacent_endpoints_of_neighbor T hp hadj hax hxb
    · obtain ⟨U,hUp,hUs,hU⟩ := separate_adjacent_endpoints_of_neighbor T hp hadj.symm hbx hxa
      exact ⟨U,hUp,hUs,hU.symm⟩
  · exact separate_nonadjacent_endpoints T hp a b hab hadj

end Erdos583AdjacentEndpointUnpairingDevelopment
