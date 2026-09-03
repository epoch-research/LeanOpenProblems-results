import Submission.MinimalCounterexample

/-!
Restrictions on vertices attaining the degree lower bound in a critical graph.
These are necessary conditions, not a settlement of Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace MinimalCounterexample
open StarElimination

/-- Two distinct vertices of degree exactly `2 * (C+1)` can belong together
in at most one piece of any cycle decomposition of a critical graph. -/
lemma IsCritical.tight_pair_inter_card {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) {u v : V} (hne : u ≠ v)
    (hu : G.degree u = 2 * (C+1)) (hv : G.degree v = 2 * (C+1)) :
    (star D u ∩ star D v).card ≤ 1 := by
  have hus : u ∈ G.support := (G.degree_pos_iff_mem_support u).mp (by omega)
  have hvs : v ∈ G.support := (G.degree_pos_iff_mem_support v).mp (by omega)
  have ht := hG.touching_card D hc hd {u,v} (Finset.insert_nonempty _ _) (by
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hus
    · exact hvs)
  simp only [touching, Finset.biUnion_insert, Finset.singleton_biUnion,
    Finset.card_pair hne] at ht
  have hdu := star_card D hc hd u
  have hdv := star_card D hc hd v
  have hi := Finset.card_union_add_card_inter (star D u) (star D v)
  omega

lemma IsCritical.eq_of_tight_pair_mem {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) {u v : V} (hne : u ≠ v)
    (hu : G.degree u = 2 * (C+1)) (hv : G.degree v = 2 * (C+1))
    {H K : G.Subgraph} (hH : H ∈ D) (hK : K ∈ D)
    (huH : u ∈ H.verts) (hvH : v ∈ H.verts)
    (huK : u ∈ K.verts) (hvK : v ∈ K.verts) : H = K := by
  have hb := hG.tight_pair_inter_card D hc hd hne hu hv
  by_contra hneHK
  have hh : H ∈ star D u ∩ star D v := by simp [mem_star, hH, huH, hvH]
  have hk : K ∈ star D u ∩ star D v := by simp [mem_star, hK, huK, hvK]
  have htwo := Finset.one_lt_card.mpr ⟨H,hh,K,hk,hneHK⟩
  omega

/-- An edge whose endpoints both attain the critical degree lower bound
cannot be a chord of any cycle in the graph. -/
lemma IsCritical.tight_edge_not_chord {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    {u v : V} (huv : G.Adj u v)
    (hu : G.degree u = 2 * (C+1)) (hv : G.degree v = 2 * (C+1))
    (H : G.Subgraph) (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (huH : u ∈ H.verts) (hvH : v ∈ H.verts) : H.Adj u v := by
  obtain ⟨D,hc,hd,hHD,_⟩ := hG.extend_cycle H hcH
  have he : s(u,v) ∈ G.edgeSet := huv
  rw [← hd.2] at he
  obtain ⟨K,hKD,heK⟩ := Set.mem_iUnion₂.mp he
  have hadj : K.Adj u v := heK
  have heq := hG.eq_of_tight_pair_mem D hc hd huv.ne hu hv hHD hKD
    huH hvH (K.edge_vert hadj) (K.edge_vert hadj.symm)
  simpa only [← heq] using hadj


/-- A finite nonempty graph with no chord in any cycle has a vertex of
degree at most two. This elementary fact is proved from a longest path. -/
lemma exists_degree_le_two_of_no_chords {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V)
    (hc : ∀ H : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      ∀ u v, u ∈ H.verts → v ∈ H.verts → G.Adj u v → H.Adj u v) :
    ∃ v, G.degree v ≤ 2 := by
  obtain ⟨u,v,p,hp,hm⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  by_cases hdu : G.degree u ≤ 2
  · exact ⟨u,hdu⟩
  have hs := longest_path_start_neighbors p hp hm
  have hne : (Finset.univ : Finset (G.neighborSet u)).Nonempty := by
    obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj u).mp (by omega)
    exact ⟨⟨w,hw⟩,Finset.mem_univ _⟩
  let f : G.neighborSet u → ℕ := fun x => (p.takeUntil x.val (hs x.val x.property)).length
  obtain ⟨x,_,hx⟩ := Finset.univ.exists_max_image f hne
  let q := p.takeUntil x.val (hs x.val x.property)
  have hq : q.IsPath := hp.takeUntil _
  have hnq : ∀ y, G.Adj u y → y ∈ q.support := by
    intro y hy
    have hle : f ⟨y,hy⟩ ≤ q.length := hx ⟨y,hy⟩ (Finset.mem_univ _)
    have hvq := q.getVert_mem_support (f ⟨y,hy⟩)
    rw [show q.getVert (f ⟨y,hy⟩) = y from
      (Walk.getVert_takeUntil (hs x.val x.property) hle).trans
        (p.getVert_length_takeUntil (hs y hy))] at hvq
    exact hvq
  have hlen : 2 ≤ q.length := by
    have hsub : G.neighborFinset u ⊆ q.support.toFinset := by
      intro y hy
      exact List.mem_toFinset.mpr (hnq y (G.mem_neighborFinset u y |>.mp hy))
    have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le q.support)
    rw [card_neighborFinset_eq_degree, Walk.length_support] at hcard
    omega
  let c := q.cons x.property.symm
  have hcy : c.IsCycle := path_close_isCycle q hq hlen x.property.symm
  have hcc := cycle_subgraph_regular G hcy
  have huC : u ∈ c.toSubgraph.verts := by
    apply c.mem_verts_toSubgraph.mpr
    simp only [c,Walk.support_cons,List.mem_cons]
    exact Or.inr q.start_mem_support
  have heq : c.toSubgraph.neighborSet u = G.neighborSet u := by
    ext y
    constructor
    · exact c.toSubgraph.adj_sub
    · intro hy
      apply hc c.toSubgraph hcc u y huC
      · apply c.mem_verts_toSubgraph.mpr
        simp only [c,Walk.support_cons,List.mem_cons]
        exact Or.inr (hnq y hy)
      · exact hy
  have hdegree := hcc.2 ⟨u,huC⟩
  rw [Subgraph.coe_degree] at hdegree
  simp only [Subgraph.degree,heq,← Nat.card_eq_fintype_card] at hdegree
  have hdegree' : G.degree u = 2 := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hdegree
  exact ⟨u,by omega⟩


/-- The subgraph induced by the tight-degree vertices is two-degenerate:
every nonempty induced subgraph of it has a vertex of degree at most two. -/
lemma IsCritical.tight_induce_low_degree {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (S : Set V) (hne : S.Nonempty)
    (hS : ∀ v ∈ S, G.degree v = 2 * (C+1)) :
    ∃ v : S, (G.induce S).degree v ≤ 2 := by
  letI : Nonempty S := hne.to_subtype
  apply exists_degree_le_two_of_no_chords (G.induce S)
  intro H hcH u v huH hvH huv
  let f : G.induce S →g G := (SimpleGraph.Embedding.induce S).toHom
  have hcM := subgraph_image_cycle_of_injective f Subtype.val_injective H hcH.1
    (by
      intro w
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcH.2 w)
  have hM := hG.tight_edge_not_chord (f.map_adj huv) (hS u.val u.property)
    (hS v.val v.property) (H.map f) (by
      refine ⟨hcM.1,?_⟩
      intro w
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcM.2 w)
    (show f u ∈ (H.map f).verts from ⟨u,huH,rfl⟩)
    (show f v ∈ (H.map f).verts from ⟨v,hvH,rfl⟩)
  change ∃ x y, H.Adj x y ∧ f x = f u ∧ f y = f v at hM
  obtain ⟨x,y,hxy,hx,hy⟩ := hM
  have hx' : x = u := Subtype.val_injective hx
  have hy' : y = v := Subtype.val_injective hy
  simpa only [hx',hy'] using hxy

/-- At least one nonisolated vertex exceeds the critical degree lower bound
when C is positive. This does not give a bound on that excess. -/
lemma IsCritical.exists_degree_above_tight {V : Type*} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G) (hC : 0 < C) :
    ∃ v ∈ G.support, 2 * (C+1) < G.degree v := by
  by_contra! hn
  have ht : ∀ v ∈ G.support, G.degree v = 2 * (C+1) := by
    intro v hv
    exact Nat.le_antisymm (hn v hv) (hG.degree_lower v hv)
  obtain ⟨u,v,huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG.ne_bot
  have hne : G.support.Nonempty := ⟨u,⟨v,huv⟩⟩
  obtain ⟨w,hw⟩ := hG.tight_induce_low_degree G.support hne ht
  have hdeg := SimpleGraph.degree_induce_of_support_subset (G := G)
    (Set.Subset.refl G.support) w
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg hw
  have ht' := ht w.val w.property
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at ht'
  omega


end MinimalCounterexample
end Erdos184
