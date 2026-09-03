import Submission.Work

/-! Restoration of a matching on an acyclic even-degree induced graph.
This proves the perfect-matching case and, more generally, the case with
at most three unmatched even-degree vertices. -/
open SimpleGraph Erdos583Work
namespace Erdos583EvenMatchingRestoreDevelopment
set_option maxHeartbeats 1200000

lemma even_forest_delete_even_edge {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V}
    (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v)))
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic) :
    ((G.deleteEdges {s(v,u)}).induce
      {x | Even (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet x))}).IsAcyclic := by
  classical
  let J := G.deleteEdges {s(v,u)}
  have hsub (x : V) (hx : Even (Nat.card (J.neighborSet x))) :
      Even (Nat.card (G.neighborSet x)) := by
    by_cases hxv : x=v
    · subst x; exact hv
    by_cases hxu : x=u
    · subst x; exact hu
    have he : Nat.card (J.neighborSet x)=Nat.card (G.neighborSet x) := by
      simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
      exact degree_delete_edge_other G hxv hxu
    rwa [he] at hx
  let f : J.induce {x | Even (Nat.card (J.neighborSet x))} →g
      G.induce {x | Even (Nat.card (G.neighborSet x))} :=
    { toFun := fun x ↦ ⟨x.val,hsub x.val x.property⟩
      map_rel' := fun hxy ↦ G.deleteEdges_le _ hxy }
  exact hf.comap f (by
    intro a b hab
    have hh := congrArg (fun z : {x : V // Even (Nat.card (G.neighborSet x))} ↦ z.val) hab
    exact Subtype.ext hh)

lemma matching_delete_endpoints {V : Type*} {F : SimpleGraph V}
    (hm : ∀ x, (F.neighborSet x).Subsingleton) {u v x y : V} (h : F.Adj v u)
    (hxy : (F.deleteEdges {s(v,u)}).Adj x y) : x ≠ v ∧ x ≠ u := by
  have hp : F.Adj x y ∧ s(x,y) ≠ s(v,u) := by
    simpa only [deleteEdges_adj,Set.mem_singleton_iff] using hxy
  constructor
  · rintro rfl
    have hy : y=u := hm _ hp.1 h
    exact hp.2 (by rw [hy])
  · rintro rfl
    have hy : y=v := hm _ hp.1 h.symm
    exact hp.2 (by rw [hy]; exact Sym2.eq_swap)

/-- Removing an arbitrary matching on even vertices and then restoring it
preserves every available path budget when the final even-induced graph is a
forest. The intermediate graphs need not be connected. -/
lemma restore_even_matching {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic)
    (k : ℕ)
    (hbase : ∃ D : Finset (G \ F).Subgraph, GoodDecomposition (G \ F) D ∧ D.card ≤ k) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  induction hn : F.edgeSet.ncard using Nat.strong_induction_on generalizing G F with
  | h n ih =>
    by_cases hbot : F=⊥
    · have hEq : G \ F=G := by
        ext a b
        simp only [hbot,sdiff_adj,bot_adj,not_false_eq_true,and_true]
      rw [hEq] at hbase
      exact hbase
    obtain ⟨v,u,h⟩ := ne_bot_iff_exists_adj.mp hbot
    let J := G.deleteEdges {s(v,u)}
    let K := F.deleteEdges {s(v,u)}
    have hKJ : K ≤ J := deleteEdges_mono hFG
    have hKm : ∀ x, (K.neighborSet x).Subsingleton := by
      intro x a ha b hb
      exact hm x (F.deleteEdges_le _ ha) (F.deleteEdges_le _ hb)
    have hKe : ∀ ⦃x y⦄, K.Adj x y → Even (Nat.card (J.neighborSet x)) := by
      intro x y hxy
      obtain ⟨hxv,hxu⟩ := matching_delete_endpoints hm h hxy
      have heq : Nat.card (J.neighborSet x)=Nat.card (G.neighborSet x) := by
        simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
        exact degree_delete_edge_other G hxv hxu
      rw [heq]
      exact he (F.deleteEdges_le _ hxy)
    have hJf := even_forest_delete_even_edge (u := u) (v := v) (he h.symm) (he h) hf
    have hdiff : J \ K=G \ F := by
      ext a b
      simp only [J,K,sdiff_adj,deleteEdges_adj,Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨hab,hne⟩,hn⟩
        exact ⟨hab,fun hF ↦ hn ⟨hF,hne⟩⟩
      · rintro ⟨hab,hn⟩
        refine ⟨⟨hab,?_⟩,fun hh ↦ hn hh.1⟩
        intro heq
        exact hn ((F.adj_congr_of_sym2 heq).mpr h)
    have hlt : K.edgeSet.ncard<n := by
      rw [←hn]
      change (F.deleteEdges {s(v,u)}).edgeSet.ncard < F.edgeSet.ncard
      rw [edgeSet_deleteEdges]
      exact Set.ncard_diff_singleton_lt_of_mem (show s(v,u) ∈ F.edgeSet from h)
    have hbaseJ : ∃ D : Finset (J \ K).Subgraph,
        GoodDecomposition (J \ K) D ∧ D.card ≤ k := by
      rw [hdiff]
      exact hbase
    obtain ⟨D,hD,hcard⟩ := ih K.edgeSet.ncard hlt J K hKJ hKm hKe hJf hbaseJ rfl
    exact EdgeCritical.restore_even_even_edge_of_even_forest
      (hFG h) (he h.symm) (he h) hf D hD hcard

lemma even_after_matching_iff {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x))) (x : V) :
    Even (Nat.card ((G \ F).neighborSet x)) ↔
      Even (Nat.card (G.neighborSet x)) ∧ F.neighborSet x=∅ := by
  have hs := neighbor_ncard_sdiff_add hFG x
  simp only [←Nat.card_coe_set_eq] at hs
  by_cases hempty : F.neighborSet x=∅
  · have hz : Nat.card (F.neighborSet x)=0 := by simp [hempty]
    have hdeg : Nat.card ((G \ F).neighborSet x)=Nat.card (G.neighborSet x) := by omega
    simp only [hdeg,hempty,and_true]
  · obtain ⟨y,hy⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hset : F.neighborSet x={y} := (hm x).eq_singleton_of_mem hy
    have hc : Nat.card (F.neighborSet x)=1 := by simp [hset]
    have hev := he hy
    have hn : ¬Even (Nat.card ((G \ F).neighborSet x)) := by
      rw [Nat.even_iff] at hev ⊢
      omega
    simp only [hn,hempty,and_false]

/-- A perfect matching of the even-degree vertices suffices under the
even-forest hypothesis; no connectivity assumption is needed. -/
lemma even_forest_perfect_matching {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (hcover : ∀ x, Even (Nat.card (G.neighborSet x)) → (F.neighborSet x).Nonempty)
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V := by
  classical
  have ho (x : V) : Odd (Nat.card ((G \ F).neighborSet x)) := by
    apply Nat.not_even_iff_odd.mp
    intro hx
    obtain ⟨hev,hempty⟩ := (even_after_matching_iff G F hFG hm he x).mp hx
    exact (hcover x hev).ne_empty hempty
  obtain ⟨D,hD,hcard⟩ := TrailNormalization.all_odd_path_partition (G \ F) (by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using ho)
  obtain ⟨E,hE,hEc⟩ := restore_even_matching G F hFG hm he hf D.card ⟨D,hD,le_rfl⟩
  exact ⟨E,hE,by omega⟩

/-- More generally the matching may leave up to three even vertices uncovered. -/
lemma even_forest_matching_deficiency_le_three {V : Type*} [Fintype V]
    (G F : SimpleGraph V) (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic)
    (hsmall : {x : V | Even (Nat.card (G.neighborSet x)) ∧ F.neighborSet x=∅}.ncard ≤ 3) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  apply restore_even_matching G F hFG hm he hf
  apply EndpointSelection.gallai_of_at_most_three_even (G \ F)
  have hset : {x : V | Even (Nat.card ((G \ F).neighborSet x))}=
      {x : V | Even (Nat.card (G.neighborSet x)) ∧ F.neighborSet x=∅} := by
    ext x; exact even_after_matching_iff G F hFG hm he x
  rw [←hset] at hsmall
  simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,
    Set.ncard_eq_toFinset_card',Set.toFinset_setOf] using hsmall

end Erdos583EvenMatchingRestoreDevelopment
