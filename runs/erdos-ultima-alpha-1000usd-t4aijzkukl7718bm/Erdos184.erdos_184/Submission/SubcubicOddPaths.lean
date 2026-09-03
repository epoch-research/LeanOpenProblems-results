import Submission.CoveredPathParity
import Submission.EndpointPathReversal

/-! Every finite all-odd subcubic graph has a simple-path partition with exactly
half as many paths as vertices. The arbitrary-degree case and Erdős184 remain
unproved. The proof maximizes covered edges and absorbs any unused cycle. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Piece.degree_of_mem_support (p : Piece G) {v : V} (hv : v ∈ p.walk.support) :
    p.walk.toSubgraph.spanningCoe.degree v = if v = p.src ∨ v = p.dst then 1 else 2 := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  change (p.walk.toSubgraph.neighborSet v).ncard = _
  by_cases hs : v = p.src
  · subst v
    rw [if_pos (Or.inl rfl),p.isPath.neighborSet_toSubgraph_startpoint
      (p.walk.not_nil_of_ne p.ne)]
    exact Set.ncard_singleton _
  · by_cases ht : v = p.dst
    · subst v
      rw [if_pos (Or.inr rfl),p.isPath.neighborSet_toSubgraph_endpoint
        (p.walk.not_nil_of_ne p.ne)]
      exact Set.ncard_singleton _
    · rw [if_neg (not_or.mpr ⟨hs,ht⟩)]
      obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      have hi0 : i ≠ 0 := by rintro rfl; exact hs (by simpa using hi.symm)
      have hil' : i < p.walk.length := by
        by_contra hn
        have he : i = p.walk.length := by omega
        exact ht (by simpa [he] using hi.symm)
      rw [← hi]
      exact p.isPath.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil'

lemma Piece.degree_pos_of_mem_support (p : Piece G) {v : V} (hv : v ∈ p.walk.support) :
    0 < p.walk.toSubgraph.spanningCoe.degree v := by
  rw [p.degree_of_mem_support hv]
  split_ifs <;> omega

omit [Fintype V] in
lemma coveredGraph_perm {L M : List (Piece G)} (h : L.Perm M) :
    coveredGraph L = coveredGraph M := by
  ext u v
  rw [coveredGraph_adj,coveredGraph_adj]
  exact (edgeList_perm h).mem_iff

omit [Fintype V] in
lemma pieceGraph_le_covered {L : List (Piece G)} {p : Piece G} (hp : p ∈ L) :
    p.walk.toSubgraph.spanningCoe ≤ coveredGraph L := by
  intro u v huv
  apply (coveredGraph_adj L u v).mpr
  exact List.mem_flatMap.mpr ⟨p,hp,p.walk.mem_edges_toSubgraph.mp huv⟩

lemma Admissible.two_piece_degree_le {L : List (Piece G)} (hL : Admissible L)
    {p q : Piece G} (hp : p ∈ L) (hq : q ∈ L) (hne : q ≠ p) (v : V) :
    p.walk.toSubgraph.spanningCoe.degree v + q.walk.toSubgraph.spanningCoe.degree v ≤
      (coveredGraph L).degree v := by
  obtain ⟨M,hM⟩ := two_at_front hp hq hne
  have hn := (hL.perm hM).1
  change (p.walk.edges ++ (q.walk.edges ++ edgeList M)).Nodup at hn
  have h1 := coveredGraph_cons_degree p (q :: M) hn.disjoint v
  have h2 := coveredGraph_cons_degree q M hn.of_append_right.disjoint v
  have he := coveredGraph_perm hM
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h1 h2 ⊢
  rw [he,h1,h2]
  omega

lemma Admissible.covered_degree_one_on_unused_cycle {L : List (Piece G)}
    (hL : Admissible L) (hdeg : ∀ v, G.degree v ≤ 3)
    {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hdis : (edgeList L).Disjoint c.edges) {v : V} (hv : v ∈ c.support) :
    (coveredGraph L).degree v = 1 := by
  have hle : coveredGraph L ≤ G \ c.toSubgraph.spanningCoe := by
    intro x y hxy
    refine ⟨coveredGraph_le L hxy,?_⟩
    intro hc'
    exact hdis ((coveredGraph_adj L x y).mp hxy) (c.mem_edges_toSubgraph.mp hc')
  have hb := (coveredGraph L).degree_le_of_le (v := v) hle
  have hd := degree_sdiff_add G c.toSubgraph.spanningCoe c.toSubgraph.spanningCoe_le v
  have hc2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
  have ho := Nat.odd_iff.mp (hL.covered_odd v)
  have hg := hdeg v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hb hd ho hg ⊢
  change Nat.card (c.toSubgraph.spanningCoe.neighborSet v) = 2 at hc2
  omega

lemma Admissible.path_meets_unused_cycle_at_ends {L : List (Piece G)}
    (hL : Admissible L) (hdeg : ∀ v, G.degree v ≤ 3)
    {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hdis : (edgeList L).Disjoint c.edges) {p : Piece G} (hp : p ∈ L)
    {v : V} (hv : v ∈ p.walk.support) (hvc : v ∈ c.support) :
    v = p.src ∨ v = p.dst := by
  have h1 := hL.covered_degree_one_on_unused_cycle hdeg c hc hdis hvc
  have hpdeg := p.degree_of_mem_support hv
  have hle := p.walk.toSubgraph.spanningCoe.degree_le_of_le (v := v) (pieceGraph_le_covered hp)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h1 hpdeg hle
  by_contra hn
  rw [if_neg hn] at hpdeg
  omega

lemma Admissible.paths_separate_on_unused_cycle {L : List (Piece G)}
    (hL : Admissible L) (hdeg : ∀ v, G.degree v ≤ 3)
    {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hdis : (edgeList L).Disjoint c.edges) {p q : Piece G}
    (hp : p ∈ L) (hq : q ∈ L) (hne : q ≠ p)
    {v : V} (hvc : v ∈ c.support) (hvp : v ∈ p.walk.support) :
    v ∉ q.walk.support := by
  intro hvq
  have h1 := hL.covered_degree_one_on_unused_cycle hdeg c hc hdis hvc
  have hb := hL.two_piece_degree_le hp hq hne v
  have hp' := p.degree_pos_of_mem_support hvp
  have hq' := q.degree_pos_of_mem_support hvq
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h1 hb hp' hq'
  omega

lemma Admissible.cycle_ended_paths_disjoint {L : List (Piece G)}
    (hL : Admissible L) (hdeg : ∀ v, G.degree v ≤ 3)
    {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hdis : (edgeList L).Disjoint c.edges) {p q : Piece G}
    (hp : p ∈ L) (hq : q ∈ L) (hne : q ≠ p)
    (hpa : p.src ∈ c.support) (hpb : p.dst ∈ c.support)
    (hqa : q.src ∈ c.support) (hqb : q.dst ∈ c.support) :
    p.walk.support.Disjoint q.walk.support := by
  intro v hvp hvq
  have hvc : v ∉ c.support := by
    intro hv
    exact hL.paths_separate_on_unused_cycle hdeg c hc hdis hp hq hne hv hvp hvq
  have hpe : ¬ (v = p.src ∨ v = p.dst) := by rintro (rfl | rfl) <;> contradiction
  have hqe : ¬ (v = q.src ∨ v = q.dst) := by rintro (rfl | rfl) <;> contradiction
  have hpdeg := p.degree_of_mem_support hvp
  have hqdeg := q.degree_of_mem_support hvq
  rw [if_neg hpe] at hpdeg
  rw [if_neg hqe] at hqdeg
  have hb := hL.two_piece_degree_le hp hq hne v
  have hle := (coveredGraph L).degree_le_of_le (v := v) (coveredGraph_le L)
  have hg := hdeg v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hpdeg hqdeg hb hle hg
  omega

omit [Fintype V] in
lemma support_subset_of_edges_subset_paths {a b x y : V}
    (p : G.Walk a b) (q : G.Walk x y) (hn : ¬ p.Nil) (he : p.edges ⊆ q.edges) :
    p.support ⊆ q.support := by
  intro v hv
  obtain ⟨e,hpe,hve⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hn).mp hv
  exact Walk.mem_support_of_mem_edges (he hpe) hve

lemma Maximal.head_other_end_on_unused_cycle {p : Piece G} {L : List (Piece G)}
    (hL : Maximal (p :: L)) (hdeg : ∀ v, G.degree v ≤ 3)
    {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hdis : (edgeList (p :: L)).Disjoint c.edges) (hp : p.dst ∈ c.support) :
    p.src ∈ c.support := by
  by_contra hpa
  have hcard := hc.ncard_neighborSet_toSubgraph_eq_two hp
  obtain ⟨v,hv⟩ := (Set.ncard_pos (s := c.toSubgraph.neighborSet p.dst)).mp (show 0 < (c.toSubgraph.neighborSet p.dst).ncard by omega)
  have huv : G.Adj p.dst v := c.toSubgraph.adj_sub hv
  have he : s(p.dst,v) ∈ c.edges := c.mem_edges_toSubgraph.mp hv
  have hvc : v ∈ c.support := c.snd_mem_support_of_mem_edges he
  have hva : v ≠ p.src := by rintro rfl; contradiction
  obtain ⟨q,M,hM,hqv,hperm⟩ := exists_initial_second hL v hva huv.ne.symm
  subst v
  have hdisM : (edgeList (p :: q :: M)).Disjoint c.edges := by
    intro e he hc'
    exact hdis (hperm.mem_iff.mp he) hc'
  have hne := hM.1.second_ne_first
  have huq : p.dst ∉ q.walk.support := hM.1.paths_separate_on_unused_cycle
    hdeg c hc hdisM (by simp) (by simp) hne hp p.walk.end_mem_support
  obtain ⟨r,hr,hrperm⟩ := CertificateStructure.cycle_edge_cons c hc huv he
  have hrs : r.support ⊆ c.support := by
    apply support_subset_of_edges_subset_paths r c (r.not_nil_of_ne huv.ne.symm)
    intro e he
    exact hrperm.mem_iff.mp (List.mem_cons_of_mem _ he)
  have hclean : ∀ x, x ∈ p.walk.support → x ∈ r.support → x = p.dst := by
    intro x hx hrx
    have hxc := hrs hrx
    rcases hM.1.path_meets_unused_cycle_at_ends hdeg c hc hdisM (by simp) hx hxc with h | h
    · exact (hpa (h ▸ hxc)).elim
    · exact h
  have hdisr : (edgeList (p :: q :: M)).Disjoint (Walk.cons huv r).edges := by
    intro e he hr'
    exact hdisM he (hrperm.mem_iff.mp hr')
  exact huq (hM.cons_pair_clean_blocked huv r hr hdisr hclean)

lemma Maximal.path_endpoints_on_unused_cycle {L : List (Piece G)}
    (hL : Maximal L) (hdeg : ∀ v, G.degree v ≤ 3)
    {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hdis : (edgeList L).Disjoint c.edges) {p : Piece G} (hp : p ∈ L)
    (hv : p.src ∈ c.support ∨ p.dst ∈ c.support) :
    p.src ∈ c.support ∧ p.dst ∈ c.support := by
  have hperm := List.perm_cons_erase hp
  have hM := hL.perm hperm
  have hdisM : (edgeList (p :: L.erase p)).Disjoint c.edges := by
    intro e he hc'
    exact hdis ((edgeList_perm hperm).mem_iff.mpr he) hc'
  rcases hv with hv | hv
  · refine ⟨hv,?_⟩
    apply hM.reverse_first.head_other_end_on_unused_cycle hdeg c hc _ hv
    intro e he hc'
    exact hdisM ((reverse_first_edge_perm p _).mem_iff.mp he) hc'
  · exact ⟨hM.head_other_end_on_unused_cycle hdeg c hc hdisM hv,hv⟩

lemma Maximal.no_unused_cycle_subcubic {L : List (Piece G)}
    (hL : Maximal L) (hdeg : ∀ v, G.degree v ≤ 3)
    {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hdis : (edgeList L).Disjoint c.edges) : False := by
  obtain ⟨p,M,hM,hpz,hperm⟩ := exists_terminal_head hL z
  have hdisM : (edgeList (p :: M)).Disjoint c.edges := by
    intro e he hc'
    exact hdis (hperm.mem_iff.mp he) hc'
  have hpd : p.dst ∈ c.support := by rw [hpz]; exact c.start_mem_support
  have hpa := hM.head_other_end_on_unused_cycle hdeg c hc hdisM hpd
  have hcard := hc.ncard_neighborSet_toSubgraph_eq_two hpd
  have hv : ∃ v, c.toSubgraph.Adj p.dst v ∧ v ≠ p.src := by
    by_contra! hn
    have hsub : c.toSubgraph.neighborSet p.dst ⊆ {p.src} := fun v hv => hn v hv
    have hh := Set.ncard_le_ncard hsub
    rw [hcard,Set.ncard_singleton] at hh
    omega
  obtain ⟨v,hv,hva⟩ := hv
  have huv : G.Adj p.dst v := c.toSubgraph.adj_sub hv
  have he : s(p.dst,v) ∈ c.edges := c.mem_edges_toSubgraph.mp hv
  have hvc := c.snd_mem_support_of_mem_edges he
  obtain ⟨q,N,hN,hqv,hpermN⟩ := exists_initial_second hM v hva huv.ne.symm
  subst v
  have hdisN : (edgeList (p :: q :: N)).Disjoint c.edges := by
    intro e he hc'
    exact hdisM (hpermN.mem_iff.mp he) hc'
  have hne := hN.1.second_ne_first
  have hqb := (hN.path_endpoints_on_unused_cycle hdeg c hc hdisN (by simp)
    (Or.inl hvc)).2
  have hpq : p.walk.support.Disjoint q.walk.support :=
    hN.1.cycle_ended_paths_disjoint hdeg c hc hdisN (by simp) (by simp) hne hpa hpd hvc hqb
  obtain ⟨r,hr,hrperm⟩ := CertificateStructure.cycle_edge_cons c hc huv he
  have hdisr : (edgeList (p :: q :: N)).Disjoint (Walk.cons huv r).edges := by
    intro e he hr'
    exact hdisN he (hrperm.mem_iff.mp hr')
  exact hN.cons_pair_not_disjoint huv r hr hdisr hpq

/-- The residual of a maximal endpoint-path packing is acyclic in a subcubic graph. -/
lemma Maximal.residual_acyclic_subcubic {L : List (Piece G)}
    (hL : Maximal L) (hdeg : ∀ v, G.degree v ≤ 3) :
    (G \ coveredGraph L).IsAcyclic := by
  intro z c hc
  have hle : G \ coveredGraph L ≤ G := sdiff_le
  apply hL.no_unused_cycle_subcubic hdeg (c.mapLe hle) (hc.mapLe hle)
  intro e he hc'
  have hcr : e ∈ (G \ coveredGraph L).edgeSet :=
    c.edges_subset_edgeSet (by simpa only [Walk.edges_mapLe_eq_edges] using hc')
  rw [SimpleGraph.edgeSet_sdiff] at hcr
  exact hcr.2 ((coveredGraph_edgeSet L e).mpr he)

/-- In an all-odd subcubic graph the maximal family covers every edge. -/
lemma Maximal.covers_subcubic {L : List (Piece G)} (hL : Maximal L)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    ∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L := by
  have hb : G \ coveredGraph L = ⊥ := by
    apply acyclic_even_eq_bot (G \ coveredGraph L) (hL.residual_acyclic_subcubic hdeg)
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      hL.1.residual_even hodd v
  have hle : G ≤ coveredGraph L := sdiff_eq_bot_iff.mp hb
  intro e
  refine ⟨fun he => (coveredGraph_edgeSet L e).mp (SimpleGraph.edgeSet_mono hle he),?_⟩
  intro he
  exact edgeList_mem_edgeSet he

/-- Every all-odd finite graph of maximum degree at most three has a simple-path
partition with exactly half as many paths as vertices, and unique endpoints. -/
lemma subcubic_all_odd_path_partition (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    ∃ L : List (Piece G),
      Admissible L ∧ (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L) ∧
      2 * L.length = Fintype.card V := by
  obtain ⟨L,hL⟩ := exists_maximal G hodd
  exact ⟨L,hL.1,hL.covers_subcubic hdeg hodd,hL.1.path_count⟩

end Erdos184Work.OddPaths

#print axioms Erdos184Work.OddPaths.Admissible.cycle_ended_paths_disjoint

#print axioms Erdos184Work.OddPaths.Maximal.no_unused_cycle_subcubic
#print axioms Erdos184Work.OddPaths.subcubic_all_odd_path_partition
