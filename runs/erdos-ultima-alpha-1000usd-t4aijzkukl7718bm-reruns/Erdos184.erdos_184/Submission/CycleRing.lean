import Submission.CycleMixing

/-! Replacing a clean ring of cycle pieces by two cycles.
This is an auxiliary replacement lemma, not a linear bound for general graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace CycleRing

variable {V : Type*} {G : SimpleGraph V}

/-- Concatenate a finite sequence of walks with prescribed successive endpoints. -/
def chain (v : ℕ → V) : (n : ℕ) →
    (∀ i, i < n → G.Walk (v i) (v (i+1))) → G.Walk (v 0) (v n)
  | 0, _ => .nil
  | n+1, p => (chain v n (fun i hi => p i (Nat.lt_succ_of_lt hi))).append (p n (by omega))

lemma mem_edges_chain (v : ℕ → V) (n : ℕ)
    (p : ∀ i, i < n → G.Walk (v i) (v (i+1))) (e : Sym2 V) :
    e ∈ (chain v n p).edges ↔ ∃ i, ∃ hi : i < n, e ∈ (p i hi).edges := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    simp only [chain, Walk.edges_append, List.mem_append, ih]
    constructor
    · rintro (⟨i, hi, he⟩ | he)
      · exact ⟨i, Nat.lt_succ_of_lt hi, he⟩
      · exact ⟨n, by omega, he⟩
    · rintro ⟨i, hi, he⟩
      by_cases hin : i < n
      · exact Or.inl ⟨i, hin, he⟩
      · have : i = n := by omega
        subst i
        exact Or.inr he

lemma mem_tail_chain (v : ℕ → V) (n : ℕ)
    (p : ∀ i, i < n → G.Walk (v i) (v (i+1))) (x : V) :
    x ∈ (chain v n p).support.tail ↔
      ∃ i, ∃ hi : i < n, x ∈ (p i hi).support.tail := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    simp only [chain, Walk.tail_support_append, List.mem_append, ih]
    constructor
    · rintro (⟨i, hi, hx⟩ | hx)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
      · exact ⟨n, by omega, hx⟩
    · rintro ⟨i, hi, hx⟩
      by_cases hin : i < n
      · exact Or.inl ⟨i, hin, hx⟩
      · have : i = n := by omega
        subst i
        exact Or.inr hx

lemma chain_isTrail (v : ℕ → V) (n : ℕ)
    (p : ∀ i, i < n → G.Walk (v i) (v (i+1)))
    (hp : ∀ i hi, (p i hi).IsTrail)
    (hd : ∀ i hi j hj, i ≠ j → (p i hi).edges.Disjoint (p j hj).edges) :
    (chain v n p).IsTrail := by
  induction n with
  | zero => exact Walk.IsTrail.nil
  | succ n ih =>
    rw [Walk.isTrail_def, chain, Walk.edges_append, List.nodup_append']
    refine ⟨(ih _ (fun i hi => hp i _) (fun i hi j hj h => hd i _ j _ h)).edges_nodup,
      (hp n _).edges_nodup, ?_⟩
    intro e he hn
    obtain ⟨i, hi, he⟩ := (mem_edges_chain _ _ _ _).mp he
    exact hd i _ n _ (by omega) he hn

lemma chain_tail_nodup (v : ℕ → V) (n : ℕ)
    (p : ∀ i, i < n → G.Walk (v i) (v (i+1)))
    (hp : ∀ i hi, (p i hi).support.tail.Nodup)
    (hd : ∀ i hi j hj, i ≠ j →
      (p i hi).support.tail.Disjoint (p j hj).support.tail) :
    (chain v n p).support.tail.Nodup := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    rw [chain, Walk.tail_support_append, List.nodup_append']
    refine ⟨ih _ (fun i hi => hp i _) (fun i hi j hj h => hd i _ j _ h), hp n _, ?_⟩
    intro x hx hn
    obtain ⟨i, hi, hx⟩ := (mem_tail_chain _ _ _ _).mp hx
    exact hd i _ n _ (by omega) hx hn

lemma chain_isCycle (v : ℕ → V) (n : ℕ)
    (p : ∀ i, i < n → G.Walk (v i) (v (i+1)))
    (hclose : v n = v 0) (hn : 0 < n) (hne : v 0 ≠ v 1)
    (hp : ∀ i hi, (p i hi).IsPath)
    (hedge : ∀ i hi j hj, i ≠ j → (p i hi).edges.Disjoint (p j hj).edges)
    (htail : ∀ i hi j hj, i ≠ j →
      (p i hi).support.tail.Disjoint (p j hj).support.tail) :
    ((chain v n p).copy rfl hclose).IsCycle := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (Walk.isTrail_copy _ _ _).mpr (chain_isTrail v n p (fun i hi => (hp i hi).isTrail) hedge)
  · intro hnil
    have hm : v 1 ∈ (chain v n p).support.tail := by
      apply (mem_tail_chain _ _ _ _).mpr
      exact ⟨0, hn, Walk.end_mem_tail_support_of_ne hne (p 0 hn)⟩
    have hc : ((chain v n p).copy rfl hclose).support.tail = [] := by rw [hnil]; rfl
    simp only [Walk.support_copy] at hc
    rw [hc] at hm
    exact List.not_mem_nil hm
  · simpa only [Walk.support_copy] using
      chain_tail_nodup v n p (fun i hi => (hp i hi).support_nodup.tail) htail

/-- Two directed arcs obtained by splitting a cycle at a different vertex. -/
lemma split_cycle {u w : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hw : w ∈ c.support) (hne : u ≠ w) :
    ∃ p q : G.Walk u w,
      p.IsPath ∧ q.IsPath ∧ p.edges.Disjoint q.edges ∧
      (∀ e, e ∈ p.edges ∨ e ∈ q.edges ↔ e ∈ c.edges) ∧
      p.support ⊆ c.support ∧ q.support ⊆ c.support := by
  let p := c.takeUntil w hw
  let q := (c.dropUntil w hw).reverse
  have hp : p.IsPath := hc.isPath_takeUntil hw
  have hq : q.IsPath := by
    apply Walk.IsPath.reverse
    apply Walk.IsCycle.isPath_of_append_right (p := c.takeUntil w hw) (Walk.not_nil_of_ne hne)
    simpa only [Walk.take_spec] using hc
  refine ⟨p, q, hp, hq, ?_, ?_, c.support_takeUntil_subset hw, ?_⟩
  · simpa only [q, Walk.edges_reverse, List.disjoint_reverse_right] using
      hc.isTrail.disjoint_edges_takeUntil_dropUntil hw
  · intro e
    change e ∈ (c.takeUntil w hw).edges ∨ e ∈ (c.dropUntil w hw).reverse.edges ↔ _
    simp only [Walk.edges_reverse, List.mem_reverse, ← List.mem_append, ← Walk.edges_append,
      Walk.take_spec]
  · intro x hx
    exact c.support_dropUntil_subset hw (by simpa only [q, Walk.support_reverse, List.mem_reverse] using hx)

/-- A clean ring of cycles admits two edge-disjoint cycles with the same union of edges.
The intersection hypothesis says that two distinct original pieces can meet only at
one of their two chosen initial junctions. -/
lemma replacement (v : ℕ → V) (n : ℕ)
    (c : ∀ i, i < n → G.Walk (v i) (v i))
    (hc : ∀ i hi, (c i hi).IsCycle)
    (hn : 0 < n) (hclose : v n = v 0)
    (hne : ∀ i, i < n → v i ≠ v (i+1))
    (hnext : ∀ i hi, v (i+1) ∈ (c i hi).support)
    (hedge : ∀ i hi j hj, i ≠ j → (c i hi).edges.Disjoint (c j hj).edges)
    (hinter : ∀ i hi j hj, i ≠ j → ∀ x,
      x ∈ (c i hi).support → x ∈ (c j hj).support → x = v i ∨ x = v j) :
    ∃ P Q : G.Walk (v 0) (v 0), P.IsCycle ∧ Q.IsCycle ∧
      P.edges.Disjoint Q.edges ∧
      ∀ e, e ∈ P.edges ∨ e ∈ Q.edges ↔ ∃ i, ∃ hi : i < n, e ∈ (c i hi).edges := by
  choose p q hp hq hpq hcover hps hqs using
    fun i hi => split_cycle (c i hi) (hc i hi) (hnext i hi) (hne i hi)
  have hpe : ∀ i hi, (p i hi).edges ⊆ (c i hi).edges := by
    intro i hi e he
    exact (hcover i hi e).mp (Or.inl he)
  have hqe : ∀ i hi, (q i hi).edges ⊆ (c i hi).edges := by
    intro i hi e he
    exact (hcover i hi e).mp (Or.inr he)
  have hpedge : ∀ i hi j hj, i ≠ j → (p i hi).edges.Disjoint (p j hj).edges := by
    intro i hi j hj hij e hei hej
    exact hedge i hi j hj hij (hpe i hi hei) (hpe j hj hej)
  have hqedge : ∀ i hi j hj, i ≠ j → (q i hi).edges.Disjoint (q j hj).edges := by
    intro i hi j hj hij e hei hej
    exact hedge i hi j hj hij (hqe i hi hei) (hqe j hj hej)
  have ht : ∀ (a : ∀ i, i < n → G.Walk (v i) (v (i+1))),
      (∀ i hi, (a i hi).IsPath) → (∀ i hi, (a i hi).support ⊆ (c i hi).support) →
      ∀ i hi j hj, i ≠ j → (a i hi).support.tail.Disjoint (a j hj).support.tail := by
    intro a ha hs i hi j hj hij x hxi hxj
    have hni : v i ∉ (a i hi).support.tail := by
      have hh := (ha i hi).support_nodup
      rw [Walk.support_eq_cons, List.nodup_cons] at hh
      exact hh.1
    have hnj : v j ∉ (a j hj).support.tail := by
      have hh := (ha j hj).support_nodup
      rw [Walk.support_eq_cons, List.nodup_cons] at hh
      exact hh.1
    rcases hinter i hi j hj hij x (hs i hi (List.mem_of_mem_tail hxi))
      (hs j hj (List.mem_of_mem_tail hxj)) with rfl | rfl
    · exact hni hxi
    · exact hnj hxj
  let P := (chain v n p).copy rfl hclose
  let Q := (chain v n q).copy rfl hclose
  refine ⟨P, Q, chain_isCycle v n p hclose hn (hne 0 hn) hp hpedge (ht p hp hps),
    chain_isCycle v n q hclose hn (hne 0 hn) hq hqedge (ht q hq hqs), ?_, ?_⟩
  · intro e heP heQ
    simp only [P, Q, Walk.edges_copy] at heP heQ
    obtain ⟨i, hi, hei⟩ := (mem_edges_chain _ _ _ _).mp heP
    obtain ⟨j, hj, hej⟩ := (mem_edges_chain _ _ _ _).mp heQ
    by_cases hij : i = j
    · subst j
      exact hpq i hi hei hej
    · exact hedge i hi j hj hij (hpe i hi hei) (hqe j hj hej)
  · intro e
    simp only [P, Q, Walk.edges_copy, mem_edges_chain]
    constructor
    · rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩)
      · exact ⟨i, hi, hpe i hi he⟩
      · exact ⟨i, hi, hqe i hi he⟩
    · rintro ⟨i, hi, he⟩
      rcases (hcover i hi e).mpr he with hp | hq
      · exact Or.inl ⟨i, hi, hp⟩
      · exact Or.inr ⟨i, hi, hq⟩

/-- A globally minimum cycle decomposition contains no clean ring of three
or more distinct pieces. -/
lemma minimum_ring_size_le_two [Fintype V]
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (v : ℕ → V) (n : ℕ)
    (c : ∀ i, i < n → G.Walk (v i) (v i))
    (hc : ∀ i hi, (c i hi).IsCycle)
    (hcD : ∀ i hi, (c i hi).toSubgraph ∈ D)
    (hinj : Function.Injective (fun i : Fin n => (c i.val i.isLt).toSubgraph))
    (hn : 0 < n) (hclose : v n = v 0)
    (hne : ∀ i, i < n → v i ≠ v (i+1))
    (hnext : ∀ i hi, v (i+1) ∈ (c i hi).support)
    (hinter : ∀ i hi j hj, i ≠ j → ∀ x,
      x ∈ (c i hi).support → x ∈ (c j hj).support → x = v i ∨ x = v j) :
    n ≤ 2 := by
  have hedge : ∀ i hi j hj, i ≠ j → (c i hi).edges.Disjoint (c j hj).edges := by
    intro i hi j hj hij e hei hej
    have hne' : (c i hi).toSubgraph ≠ (c j hj).toSubgraph := by
      intro heq
      exact hij (congrArg Fin.val (hinj (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) heq))
    exact Set.disjoint_left.mp (hd.1 (hcD i hi) (hcD j hj) hne')
      ((c i hi).mem_edges_toSubgraph.mpr hei) ((c j hj).mem_edges_toSubgraph.mpr hej)
  obtain ⟨P, Q, hP, hQ, hPQ, hcover⟩ :=
    replacement v n c hc hn hclose hne hnext hedge hinter
  let S := Finset.univ.image (fun i : Fin n => (c i.val i.isLt).toSubgraph)
  let E : Finset G.Subgraph := {P.toSubgraph, Q.toSubgraph}
  have hs : S ⊆ D := by
    intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact hcD i.val i.isLt
  have hec : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact cycle_subgraph_regular G hP
    · have : H = Q.toSubgraph := Finset.mem_singleton.mp hH
      subst H
      exact cycle_subgraph_regular G hQ
  have he : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet) := by
    have hdis : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e heP heQ
      exact hPQ (P.mem_edges_toSubgraph.mp heP) (Q.mem_edges_toSubgraph.mp heQ)
    intro H hH K hK hneHK
    have hh : H = P.toSubgraph ∨ H = Q.toSubgraph := by simpa [E] using hH
    have hk : K = P.toSubgraph ∨ K = Q.toSubgraph := by simpa [E] using hK
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
    · exact (hneHK rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hneHK rfl).elim
  have hcov : (⋃ H ∈ E, H.edgeSet) = ⋃ H ∈ S, H.edgeSet := by
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, hH, heH⟩
      have hePQ : e ∈ P.edges ∨ e ∈ Q.edges := by
        have hh : H = P.toSubgraph ∨ H = Q.toSubgraph := by simpa [E] using hH
        rcases hh with rfl | rfl
        · exact Or.inl (P.mem_edges_toSubgraph.mp heH)
        · exact Or.inr (Q.mem_edges_toSubgraph.mp heH)
      obtain ⟨i, hi, hei⟩ := (hcover e).mp hePQ
      exact ⟨(c i hi).toSubgraph, Finset.mem_image.mpr ⟨⟨i,hi⟩, Finset.mem_univ _, rfl⟩,
        (c i hi).mem_edges_toSubgraph.mpr hei⟩
    · rintro ⟨H, hH, heH⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
      rcases (hcover e).mpr ⟨i.val, i.isLt, (c i.val i.isLt).mem_edges_toSubgraph.mp heH⟩ with hP | hQ
      · exact ⟨P.toSubgraph, Finset.mem_insert_self _ _, P.mem_edges_toSubgraph.mpr hP⟩
      · exact ⟨Q.toSubgraph, by simp [E], Q.mem_edges_toSubgraph.mpr hQ⟩
  have hmin := minimum_cycle_subfamily G D hD hd hm S E hs hec he hcov
  have hcardS : S.card = n := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hcardE : E.card ≤ 2 := by
    exact (Finset.card_insert_le _ _).trans (by simp)
  omega

/-- Connected regular-two subgraphs have no additional isolated vertices, so
an equality of edge sets determines an equality of subgraphs. -/
lemma cycle_piece_eq_of_edgeSet_eq [Fintype V] (H K : G.Subgraph)
    (hr : H.coe.IsRegularOfDegree 2) (kr : K.coe.IsRegularOfDegree 2)
    (he : H.edgeSet = K.edgeSet) : H = K := by
  have hv : ∀ (A B : G.Subgraph), A.coe.IsRegularOfDegree 2 →
      A.edgeSet ⊆ B.edgeSet → A.verts ⊆ B.verts := by
    intro A B hA hab v hv
    have hpos : 0 < A.coe.degree ⟨v,hv⟩ := by
      have hh := hA ⟨v,hv⟩
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
      omega
    obtain ⟨w, hw⟩ := (A.coe.degree_pos_iff_exists_adj ⟨v,hv⟩).mp hpos
    have hh : s(v,w.val) ∈ B.edgeSet := hab (show s(v,w.val) ∈ A.edgeSet from hw)
    exact B.edge_vert hh
  apply Subgraph.ext (Set.Subset.antisymm (hv H K hr he.subset) (hv K H kr he.symm.subset))
  funext u v
  exact propext (Set.ext_iff.mp he s(u,v))

/-- A cycle piece can be represented by a simple closed walk at any of its vertices. -/
lemma cycle_piece_walk_at [Fintype V] (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (v : V) (hv : v ∈ H.verts) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.toSubgraph = H := by
  have hcycles : H.coe.IsCycles := by
    intro u _
    have hh := hr u
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hh
  have hpos : 0 < H.coe.degree ⟨v,hv⟩ := by
    have hh := hr ⟨v,hv⟩
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
    omega
  have hn := (SimpleGraph.degree_pos_iff_nonempty (G := H.coe) (v := ⟨v,hv⟩)).mp hpos
  obtain ⟨p, hp, _⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.coe.connectedComponentMk ⟨v,hv⟩) ConnectedComponent.connectedComponentMk_mem hn
  let q : G.Walk v v := p.map H.hom
  have hq : q.IsCycle := hp.map Subtype.val_injective
  have hqr := cycle_subgraph_regular G hq
  have hsub : q.toSubgraph.edgeSet ⊆ H.edgeSet := by
    intro e he
    change e ∈ (p.map H.hom).toSubgraph.edgeSet at he
    rw [Walk.toSubgraph_map, Subgraph.edgeSet_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    induction a using Sym2.ind with
    | h u w =>
      exact p.toSubgraph.adj_sub ha
  have heq := cycle_piece_edge_eq_of_subset H q.toSubgraph hc hr hqr.1 hqr.2 hsub
  exact ⟨q, hq, cycle_piece_eq_of_edgeSet_eq q.toSubgraph H hqr.2 hr heq⟩

/-- Subgraph formulation of the clean-ring exclusion. -/
lemma minimum_clean_ring_subgraphs [Fintype V]
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (v : ℕ → V) (n : ℕ) (H : ∀ i, i < n → G.Subgraph)
    (hHD : ∀ i hi, H i hi ∈ D)
    (hinj : Function.Injective (fun i : Fin n => H i.val i.isLt))
    (hn : 0 < n) (hclose : v n = v 0)
    (hne : ∀ i, i < n → v i ≠ v (i+1))
    (hstart : ∀ i hi, v i ∈ (H i hi).verts)
    (hnext : ∀ i hi, v (i+1) ∈ (H i hi).verts)
    (hinter : ∀ i hi j hj, i ≠ j → ∀ x,
      x ∈ (H i hi).verts → x ∈ (H j hj).verts → x = v i ∨ x = v j) :
    n ≤ 2 := by
  choose c hc heq using fun i hi => cycle_piece_walk_at (H i hi)
    (hD _ (hHD i hi)).1 (hD _ (hHD i hi)).2 (v i) (hstart i hi)
  have hcD : ∀ i hi, (c i hi).toSubgraph ∈ D := by
    intro i hi
    rw [heq i hi]
    exact hHD i hi
  have hinj' : Function.Injective (fun i : Fin n => (c i.val i.isLt).toSubgraph) := by
    intro i j hij
    apply hinj
    simpa only [heq] using hij
  have hnext' : ∀ i hi, v (i+1) ∈ (c i hi).support := by
    intro i hi
    apply (c i hi).mem_verts_toSubgraph.mp
    rw [heq]
    exact hnext i hi
  apply minimum_ring_size_le_two D hD hd hm v n c hc hcD hinj' hn hclose hne hnext'
  intro i hi j hj hij x hxi hxj
  apply hinter i hi j hj hij x
  · rw [← heq i hi]
    exact (c i hi).mem_verts_toSubgraph.mpr hxi
  · rw [← heq j hj]
    exact (c j hj).mem_verts_toSubgraph.mpr hxj

end CycleRing
end Erdos184
