import Submission.SubcubicOddPaths

/-! Endpoint counting for a path packing with one endpoint at every vertex.
At an unused-cycle vertex there are two neighbors whose endpoint paths avoid
that vertex. This is an exchange constraint, not an absorption theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Piece.degree_add_endpoint_count (p : Piece G) (v : V) :
    p.walk.toSubgraph.spanningCoe.degree v + [p.src,p.dst].count v =
      if v ∈ p.walk.support then 2 else 0 := by
  by_cases hv : v ∈ p.walk.support
  · rw [if_pos hv,p.degree_of_mem_support hv]
    by_cases hs : v = p.src
    · subst v
      simp [p.ne]
    · by_cases ht : v = p.dst
      · subst v
        simp [hs,p.ne]
      · simp [hs,ht,Ne.symm hs,Ne.symm ht]
  · have hd : p.walk.toSubgraph.spanningCoe.degree v = 0 := by
      apply (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr
      rintro ⟨u,hu⟩
      exact hv (p.walk.fst_mem_support_of_mem_edges (p.walk.mem_edges_toSubgraph.mp hu))
    have hs : v ≠ p.src := by rintro rfl; exact hv p.walk.start_mem_support
    have ht : v ≠ p.dst := by rintro rfl; exact hv p.walk.end_mem_support
    simp [if_neg hv,hd,Ne.symm hs,Ne.symm ht]

noncomputable def touchingPaths (L : List (Piece G)) (v : V) : List (Piece G) :=
  L.filter (fun p => decide (v ∈ p.walk.support))

omit [Fintype V] in
@[simp] lemma mem_touchingPaths {L : List (Piece G)} {p : Piece G} {v : V} :
    p ∈ touchingPaths L v ↔ p ∈ L ∧ v ∈ p.walk.support := by
  simp [touchingPaths]

lemma covered_degree_add_endpoint_count (L : List (Piece G))
    (hn : (edgeList L).Nodup) (v : V) :
    (coveredGraph L).degree v + (endpoints L).count v =
      2 * (touchingPaths L v).length := by
  induction L with
  | nil =>
    simp only [coveredGraph,endpoints_nil,List.count_nil,touchingPaths,List.filter_nil,List.length_nil]
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    simp
  | cons p L ih =>
    have hn' : (p.walk.edges ++ edgeList L).Nodup := hn
    have hd := coveredGraph_cons_degree p L hn'.disjoint v
    have hh := ih hn'.of_append_right
    have hp := p.degree_add_endpoint_count v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hh hp ⊢
    change _ + (endpoints (p :: L)).count v = _
    rw [hd]
    simp only [endpoints_cons,List.count_cons,List.count_nil] at hp ⊢
    by_cases hv : v ∈ p.walk.support
    · simp only [if_pos hv] at hp
      simp only [touchingPaths,List.filter_cons,hv,decide_true,ite_true,List.length_cons]
      change _ = 2 * ((touchingPaths L v).length + 1)
      omega
    · simp only [if_neg hv] at hp
      simp only [touchingPaths,List.filter_cons,hv,decide_false]
      change _ = 2 * (touchingPaths L v).length
      omega

noncomputable def touchingEndpoints (L : List (Piece G)) (v : V) : Finset V :=
  (endpoints (touchingPaths L v)).toFinset

lemma Admissible.touchingEndpoints_card {L : List (Piece G)} (hL : Admissible L) (v : V) :
    (touchingEndpoints L v).card = (coveredGraph L).degree v + 1 := by
  have hsub : (endpoints (touchingPaths L v)).Sublist (endpoints L) :=
    List.filter_sublist.flatMap (fun p : Piece G => [p.src,p.dst])
  have hn : (endpoints (touchingPaths L v)).Nodup := hL.2.1.sublist hsub
  have he := covered_degree_add_endpoint_count L hL.1 v
  have hc : (endpoints L).count v = 1 := List.count_eq_one_of_mem hL.2.1 (hL.2.2 v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he ⊢
  rw [hc] at he
  simpa only [touchingEndpoints,List.toFinset_card_of_nodup hn,endpoints_length] using he.symm

lemma Admissible.mem_touchingEndpoints_self {L : List (Piece G)} (hL : Admissible L) (v : V) :
    v ∈ touchingEndpoints L v := by
  obtain ⟨p,hp,hv⟩ := List.mem_flatMap.mp (hL.2.2 v)
  have hvp : v ∈ p.walk.support := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    exact hv.elim (fun h => h ▸ p.walk.start_mem_support) (fun h => h ▸ p.walk.end_mem_support)
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨p,mem_touchingPaths.mpr ⟨hp,hvp⟩,hv⟩

/-- The number of neighbors not assigned to paths through `v` is at least
its residual degree. This uses simplicity and unique endpoints. -/
lemma Admissible.residual_degree_le_escaping_neighbors {L : List (Piece G)}
    (hL : Admissible L) (v : V) :
    (G \ coveredGraph L).degree v ≤ (G.neighborFinset v \ touchingEndpoints L v).card := by
  let E := touchingEndpoints L v
  have hv : v ∈ E := hL.mem_touchingEndpoints_self v
  have hsub : G.neighborFinset v ∩ E ⊆ E.erase v := by
    intro u hu
    obtain ⟨huN,huE⟩ := Finset.mem_inter.mp hu
    have hne : u ≠ v := ((G.mem_neighborFinset v u).mp huN).ne.symm
    exact Finset.mem_erase.mpr ⟨hne,huE⟩
  have hle := Finset.card_le_card hsub
  have hE := hL.touchingEndpoints_card v
  have hcard := Finset.card_sdiff_add_card_inter (G.neighborFinset v) E
  have hd := degree_sdiff_add G (coveredGraph L) (coveredGraph_le L) v
  have herase := Finset.card_erase_add_one hv
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hE hcard hd ⊢
  change E.card = _ at hE
  change _ ≤ (G.neighborFinset v \ E).card
  omega

lemma Admissible.endpoint_path_avoids_of_not_touching {L : List (Piece G)}
    (hL : Admissible L) {v u : V} (hu : u ∉ touchingEndpoints L v) :
    ∃ p ∈ L, (u = p.src ∨ u = p.dst) ∧ v ∉ p.walk.support := by
  obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp (hL.2.2 u)
  have hends : u = p.src ∨ u = p.dst := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hep
  refine ⟨p,hp,hends,?_⟩
  intro hv
  apply hu
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
    ⟨p,mem_touchingPaths.mpr ⟨hp,hv⟩,hep⟩)

/-- An unused cycle supplies two distinct neighboring endpoints whose
respective packed paths avoid the chosen cycle vertex. They may be the two
endpoints of the same packed path. -/
lemma Admissible.two_escaping_neighbors_on_unused_cycle {L : List (Piece G)}
    (hL : Admissible L) {z : V} (R : G.Walk z z) (hR : R.IsCycle)
    (hdis : (edgeList L).Disjoint R.edges) {v : V} (hv : v ∈ R.support) :
    ∃ u t : V, u ≠ t ∧ G.Adj v u ∧ G.Adj v t ∧
      (∃ p ∈ L, (u = p.src ∨ u = p.dst) ∧ v ∉ p.walk.support) ∧
      (∃ q ∈ L, (t = q.src ∨ t = q.dst) ∧ v ∉ q.walk.support) := by
  have hle : R.toSubgraph.spanningCoe ≤ G \ coveredGraph L := by
    intro a b hab
    refine ⟨R.toSubgraph.adj_sub hab,?_⟩
    intro hcov
    exact hdis ((coveredGraph_adj L a b).mp hcov) (R.mem_edges_toSubgraph.mp hab)
  have hd := R.toSubgraph.spanningCoe.degree_le_of_le (v := v) hle
  have htwo := hR.ncard_neighborSet_toSubgraph_eq_two hv
  have hesc := hL.residual_degree_le_escaping_neighbors v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hesc
  change Nat.card (R.toSubgraph.spanningCoe.neighborSet v) = 2 at htwo
  have hcard : 1 < (G.neighborFinset v \ touchingEndpoints L v).card := by omega
  obtain ⟨u,hu,t,ht,hut⟩ := Finset.one_lt_card.mp hcard
  have hu' := Finset.mem_sdiff.mp hu
  have ht' := Finset.mem_sdiff.mp ht
  exact ⟨u,t,hut,(G.mem_neighborFinset v u).mp hu'.1,(G.mem_neighborFinset v t).mp ht'.1,
    hL.endpoint_path_avoids_of_not_touching hu'.2,hL.endpoint_path_avoids_of_not_touching ht'.2⟩

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Admissible.residual_degree_le_escaping_neighbors
#print axioms Erdos184Work.OddPaths.Admissible.two_escaping_neighbors_on_unused_cycle
