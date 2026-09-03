import Submission.Work

/-! Tracked single-edge restoration and universal deletion-side endpoint obstructions.
The endpoint-selection hypotheses are explicit, not asserted to be always satisfiable. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
namespace Erdos583DeletionEndpointDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma quota_balance_one_slot_graphs {V : Type*} {H G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily H k) (S : TrailFamily G k) (j : Fin k)
    (hrest : ∀ i, i ≠ j → S.start i=T.start i ∧ S.finish i=T.finish i) (v : V) :
    S.quota v + (if T.start j=v then 1 else 0) + (if T.finish j=v then 1 else 0) =
      T.quota v + (if S.start j=v then 1 else 0) + (if S.finish j=v then 1 else 0) := by
  classical
  have hsum : (∑ i ∈ Finset.univ.erase j,
      ((if S.start i=v then 1 else 0)+(if S.finish i=v then 1 else 0) : ℕ)) =
      ∑ i ∈ Finset.univ.erase j,
        ((if T.start i=v then 1 else 0)+(if T.finish i=v then 1 else 0) : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨ha,hb⟩ := hrest i (Finset.mem_erase.mp hi).1
    rw [ha,hb]
  have hS := Finset.sum_erase_add (Finset.univ : Finset (Fin k))
    (fun i ↦ ((if S.start i=v then 1 else 0)+(if S.finish i=v then 1 else 0) : ℕ))
    (Finset.mem_univ j)
  have hT := Finset.sum_erase_add (Finset.univ : Finset (Fin k))
    (fun i ↦ ((if T.start i=v then 1 else 0)+(if T.finish i=v then 1 else 0) : ℕ))
    (Finset.mem_univ j)
  rw [←quota_eq_sum_endpoints S v] at hS
  rw [←quota_eq_sum_endpoints T v] at hT
  dsimp only at hS hT
  omega


lemma append_new_edge_tracked {V : Type*} [Fintype V] {H G : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G) (T : TrailFamily H k) (hpath : ∀ i, (T.walk i).IsPath)
    (i : Fin k) {u v : V} (hui : u=T.start i ∨ u=T.finish i)
    (h : G.Adj v u) (hnew : s(v,u) ∉ H.edgeSet)
    (hcover : G.edgeSet=insert s(v,u) H.edgeSet) :
    ∃ U : TrailFamily G k,
      G.edgeSet.ncard+k ≤ U.score+1 ∧
      (∀ x, U.quota x+(if u=x then 1 else 0) = T.quota x+(if v=x then 1 else 0)) ∧
      (v ∉ (T.walk i).support → ∀ l, (U.walk l).IsPath) ∧
      (¬(∀ l, (U.walk l).IsPath) → HasRoot U v) := by
  classical
  obtain ⟨S,_,hSq,hSi,_,hparts⟩ := orient_endpoint_start T i u hui
  have hSpath (l : Fin k) : (S.walk l).IsPath :=
    ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (S.isTrail l) (hpath l) (hparts l)
  let p (l : Fin k) := (S.walk l).mapLe hHG
  have hp (l : Fin k) : (p l).IsPath := (hSpath l).mapLe hHG
  have hpe (l : Fin k) : (p l).toSubgraph.edgeSet=(S.walk l).toSubgraph.edgeSet := by
    simp [p,Walk.mapLe]
  have h' : G.Adj v (S.start i) := by rw [hSi]; exact h
  have hne (l : Fin k) : s(v,u) ∉ (p l).toSubgraph.edgeSet := by
    rw [hpe]
    exact fun hh ↦ hnew ((S.walk l).toSubgraph.edgeSet_subset hh)
  let r := Walk.cons h' (p i)
  have hr : r.IsTrail := (hp i).isTrail.cons h' (by
    intro hh
    apply hne i
    rw [←hSi]
    exact (p i).mem_edges_toSubgraph.mpr hh)
  have hre : r.toSubgraph.edgeSet=insert s(v,u) (p i).toSubgraph.edgeSet := by
    simp [r,hSi]
  have hrbound : r.length+1 ≤ r.toSubgraph.verts.ncard+1 := by
    have hh := Set.ncard_le_ncard (show (p i).toSubgraph.verts ⊆ r.toSubgraph.verts by
      simp only [r,Walk.toSubgraph,Subgraph.verts_sup]
      exact Set.subset_union_right)
    rw [(walk_vertex_ncard_eq_iff (p i)).mpr (hp i)] at hh
    simpa only [r,Walk.length_cons] using Nat.add_le_add_right hh 1
  let a (l : Fin k) := if l=i then v else S.start l
  have hex (l : Fin k) : ∃ q : G.Walk (a l) (S.finish l), q.IsTrail ∧
      q.toSubgraph.edgeSet=(if l=i then insert s(v,u) (p l).toSubgraph.edgeSet else (p l).toSubgraph.edgeSet) ∧
      (l=i → q.toSubgraph=r.toSubgraph) ∧
      (l ≠ i → q.IsPath) ∧
      q.length+1 ≤ q.toSubgraph.verts.ncard+(if l=i then 1 else 0) := by
    by_cases hl : l=i
    · subst l
      rw [show a i=v by simp [a]]
      exact ⟨r,hr,by simpa using hre,fun _ ↦ rfl,fun hn ↦ (hn rfl).elim,by simpa using hrbound⟩
    · rw [show a l=S.start l by simp [a,hl]]
      refine ⟨p l,(hp l).isTrail,by simp [hl],fun hh ↦ (hl hh).elim,fun _ ↦ hp l,?_⟩
      rw [(walk_vertex_ncard_eq_iff (p l)).mpr (hp l)]
      simp only [if_neg hl,Nat.add_zero,le_refl]
  choose q hq hqe hqr hqp hqb using hex
  let U : TrailFamily G k :=
    { start := a, finish := S.finish, walk := q, isTrail := hq,
      disjoint := by
        intro l m hlm
        rw [hqe,hqe]
        have hd : Disjoint (p l).toSubgraph.edgeSet (p m).toSubgraph.edgeSet := by
          rw [hpe,hpe]; exact S.disjoint hlm
        by_cases hl : l=i
        · subst l
          simp only [if_neg hlm.symm]
          exact Set.disjoint_insert_left.mpr ⟨hne m,hd⟩
        · by_cases hm : m=i
          · subst m
            simp only [if_neg hl]
            exact Set.disjoint_insert_right.mpr ⟨hne l,hd⟩
          · simpa only [if_neg hl,if_neg hm] using hd
      cover := by
        intro d
        rw [hcover,Set.mem_insert_iff]
        constructor
        · rintro (rfl|hd)
          · refine ⟨i,?_⟩
            rw [hqe]; simp
          · obtain ⟨l,hl⟩ := (S.cover d).mp hd
            refine ⟨l,?_⟩
            rw [hqe,←hpe] at *
            split_ifs
            · exact Set.mem_insert_of_mem _ hl
            · exact hl
        · rintro ⟨l,hl⟩
          rw [hqe] at hl
          split_ifs at hl with hh
          · rcases hl with he|he
            · exact Or.inl he
            · exact Or.inr ((S.cover d).mpr ⟨l,by rwa [hpe] at he⟩)
          · exact Or.inr ((S.cover d).mpr ⟨l,by rwa [hpe] at hl⟩) }
  refine ⟨U,?_,?_,?_,?_⟩
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun l _ ↦ hqb l)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hh
    have hlen : ∑ l, (q l).length=G.edgeSet.ncard := U.sum_length
    have hscore : ∑ l, (q l).toSubgraph.verts.ncard=U.score := rfl
    simpa only [hlen,hscore,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh
  · intro x
    have hh := quota_balance_one_slot_graphs S U i (by
      intro l hli
      exact ⟨by simp [U,a,hli],rfl⟩) x
    have hui : U.start i=v := by simp [U,a]
    have huf : U.finish i=S.finish i := rfl
    rw [hSi,hui,huf,hSq] at hh
    omega
  · intro havoid l
    have havoid' : v ∉ (p i).support := by
      intro hv
      have hvS : v ∈ (S.walk i).support := by simpa [p,Walk.mapLe] using hv
      apply havoid
      rw [←Walk.mem_verts_toSubgraph,hparts,Walk.mem_verts_toSubgraph] at hvS
      exact hvS
    have hrP : r.IsPath := (Walk.cons_isPath_iff h' (p i)).mpr ⟨hp i,havoid'⟩
    by_cases hl : l=i
    · subst l
      exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (hq i) hrP (hqr i rfl)
    · exact hqp l hl
  · intro hn
    have hri : ¬r.IsPath := by
      intro hP
      apply hn
      intro l
      by_cases hl : l=i
      · subst l
        exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (hq i) hP (hqr i rfl)
      · exact hqp l hl
    have hv : v ∈ (p i).support := by
      by_contra hh
      exact hri ((Walk.cons_isPath_iff h' (p i)).mpr ⟨hp i,hh⟩)
    exact hasRoot_of_rep U i (by simp [U,a]) rfl h' (p i) (hqr i rfl) hr hv


lemma quota_pos_of_endpoint {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {v : V} (hv : v=T.start i ∨ v=T.finish i) :
    0 < T.quota v := by
  apply Nat.card_pos_iff.mpr
  refine ⟨?_,inferInstance⟩
  rcases hv with hv | hv
  · exact ⟨⟨(i,true),hv.symm⟩⟩
  · exact ⟨⟨(i,false),hv.symm⟩⟩

lemma endpoint_of_positive_quota {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) {v : V} (hv : 0 < T.quota v) :
    ∃ i, v=T.start i ∨ v=T.finish i := by
  obtain ⟨⟨⟨i,b⟩,hs⟩⟩ := (Nat.card_pos_iff.mp hv).1
  refine ⟨i,?_⟩
  cases b
  · exact Or.inr hs.symm
  · exact Or.inl hs.symm

/-- In a failing graph, every budget-sized path family after one-edge deletion
has the opposite endpoint on every member ending at either deleted endpoint.
No parity or forest assumption is needed for this necessary condition. -/
lemma deletion_endpoint_must_meet {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath)
    (i : Fin k) (hui : u=T.start i ∨ u=T.finish i) : v ∈ (T.walk i).support := by
  by_contra hav
  have hc : G.edgeSet=insert s(v,u) (G.deleteEdges {s(v,u)}).edgeSet := by
    rw [edgeSet_deleteEdges,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(v,u) ∈ G.edgeSet from h)).symm
  obtain ⟨U,_,_,hpath,_⟩ := append_new_edge_tracked (G.deleteEdges_le _) T hp i hui h (by simp) hc
  exact hfail (MatchingAppend.path_family_partition U (hpath hav))

/-- An existing endpoint at the other end of a deleted edge suffices for
restoration under the even-forest condition. Only one endpoint of the edge
is required to have even degree in the restored graph. -/
lemma restore_if_other_endpoint_active {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u) (hu : Even (Nat.card (G.neighborSet u)))
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath)
    (hv : 0 < T.quota v) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  by_contra hfail
  have huo : Odd (T.quota u) := (QuotaParity.quota_odd_iff T u).mpr
    (EdgeDefect.even_degree_delete_edge_odd h hu)
  obtain ⟨i,hui⟩ := endpoint_of_positive_quota T huo.pos
  have hc : G.edgeSet=insert s(v,u) (G.deleteEdges {s(v,u)}).edgeSet := by
    rw [edgeSet_deleteEdges,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(v,u) ∈ G.edgeSet from h)).symm
  obtain ⟨U,hs,hq,_,hr⟩ := append_new_edge_tracked (G.deleteEdges_le _) T hp i hui h (by simp) hc
  have hnp : ¬∀ i, (U.walk i).IsPath := by
    intro hpath
    exact hfail (MatchingAppend.path_family_partition U hpath)
  have hscore : U.score+1=G.edgeSet.ncard+k := by
    have hupper := U.score_le_edges_add
    have hne := U.score_eq_edges_add_iff.not.mpr hnp
    omega
  have hv' : 2 ≤ U.quota v := by
    have hh : U.quota v=T.quota v+1 := by simpa [h.ne.symm] using hq v
    omega
  obtain ⟨P,hP⟩ := QuotaParity.normalize_root_with_pair_of_even_forest U v hscore (hr hnp) hv' hf
  exact hfail (MatchingAppend.path_family_partition P hP)

/-- Consequently the other endpoint is inactive in EVERY budget-sized path
family of the deleted graph, whenever the original even-forest graph fails.
No selection of a preferred path partition is implicit in this statement. -/
lemma failed_even_forest_deletion_quota_zero {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} {u v : V}
    (h : G.Adj v u) (hu : Even (Nat.card (G.neighborSet u)))
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath) :
    T.quota v=0 := by
  by_contra hn
  exact hfail (restore_if_other_endpoint_active h hu hf T hp (Nat.pos_of_ne_zero hn))

/-- The same restoration criterion for an unindexed finite path partition. -/
lemma restore_if_other_endpoint_member {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u) (hu : Even (Nat.card (G.neighborSet u)))
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic)
    (D : Finset (G.deleteEdges {s(v,u)}).Subgraph)
    (hD : GoodDecomposition (G.deleteEdges {s(v,u)}) D) (hk : D.card ≤ k)
    (hv : ∃ K ∈ D, (K.neighborSet v).ncard=1) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ k := by
  obtain ⟨T,hT,hparts⟩ := EdgeDefect.decomposition_path_family D hD
  obtain ⟨K,hK,hKv⟩ := hv
  obtain ⟨i,hi⟩ := hparts K hK
  have hlocal : Odd ((T.walk i).toSubgraph.neighborSet v).ncard := by
    rw [hi,hKv]
    exact odd_one
  have hend : v=T.start i ∨ v=T.finish i :=
    ((trail_neighbor_ncard_odd_iff (T.isTrail i) v).mp hlocal).2
  obtain ⟨E,hE,hEc⟩ := restore_if_other_endpoint_active h hu hf T hT (quota_pos_of_endpoint T i hend)
  exact ⟨E,hE,hEc.trans hk⟩

/-- Every bounded deletion partition in a failing graph already uses the
whole budget; otherwise the deleted edge can simply be a new singleton. -/
lemma failed_deletion_card_eq {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (D : Finset (G.deleteEdges {s(v,u)}).Subgraph)
    (hD : GoodDecomposition (G.deleteEdges {s(v,u)}) D) (hk : D.card ≤ k) : D.card=k := by
  by_contra hn
  obtain ⟨E,hE,hEc⟩ := restore_edge h hD
  exact hfail ⟨E,hE,by omega⟩

end Erdos583DeletionEndpointDevelopment
