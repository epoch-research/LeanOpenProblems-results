import Submission.ShiftedCritical

/-!
For the equivalent shifted bound, small cycle packings preserve connectivity
and connectivity after deleting any one vertex. These are necessary conditions
on minimum counterexamples, not a proof that none exist.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ShiftedCritical
open ExactVertexSmoothing
universe u
set_option maxHeartbeats 800000

lemma IsVertexMinimal.small_packing_no_one_vertex_split {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ C) : ¬HasEvenOneVertexSplit (G \ unionPieces G P) := by
  let R := G \ unionPieces G P
  rintro ⟨A,B,hA,hB,ha,hb,hea,heb,hab,hcover,hover⟩
  have hAc := support_card_two_le A ha
  have hBc := support_card_two_le B hb
  have hsum := Set.ncard_union_add_ncard_inter A.support B.support
  rw [support_union_of_edge_cover hcover] at hsum
  have hs : R.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ R.support)
  change (G \ unionPieces G P).support.ncard ≤ Fintype.card V at hs
  obtain ⟨DA,hca,hda,hba⟩ := hG.bound_on_smaller_support A (by omega) hea
  obtain ⟨DB,hcb,hdb,hbb⟩ := hG.bound_on_smaller_support B (by omega) heb
  obtain ⟨D,hdcy,hdd,hbd⟩ := combine_decompositions hA hB hab hcover DA DB
    (fun H hH => Or.inl ⟨(hca H hH).1,by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hca H hH).2 v⟩)
    (fun H hH => Or.inl ⟨(hcb H hH).1,by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcb H hH).2 v⟩)
    hda hdb
  have heR : ∀ v, Even (R.degree v) := by
    intro v
    simpa only [R, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing G hG.1 P hc hd v
  obtain ⟨E,hce,hde,hbe⟩ := refine_even_decomposition (G \ unionPieces G P) (by
    intro v
    simpa only [R, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heR v) D (by
      intro H hH
      simpa only [IsCycleOrEdge, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hdcy H hH) hdd
  obtain ⟨F,hcF,hdF,hbF⟩ := complete_cycle_packing G P hc hd E (by
    intro H hH
    refine ⟨(hce H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hce H hH).2 v) hde
  apply hG.2.1
  refine ⟨F,hcF,hdF,?_⟩
  have hh := Nat.mul_le_mul_left C (show
    (A.support.ncard - 2) + (B.support.ncard - 2) + 1 ≤ Fintype.card V - 2 by omega)
  simp only [Nat.mul_add,Nat.mul_one] at hh
  omega

lemma packing_degree_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet)) (v : V) :
    (unionPieces G P).degree v ≤ 2 * P.card := by
  rw [unionPieces_degree G P hd]
  calc
    (∑ H ∈ P, H.degree v) ≤ ∑ _H ∈ P, 2 := by
      apply Finset.sum_le_sum
      intro H hH
      by_cases hv : v ∈ H.verts
      · have hh := (hc H hH).2 ⟨v,hv⟩
        rw [Subgraph.coe_degree] at hh
        have hh' : H.degree v = 2 := by
          simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh
        omega
      · rw [Subgraph.degree_of_notMem_verts hv]
        omega
    _ = _ := by simp [mul_comm]

lemma IsVertexMinimal.small_packing_degree_lower {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 0 < C)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ C) (v : V) : 4 ≤ (G \ unionPieces G P).degree v := by
  have hGv := hG.degree_lower hC v
  have hPv := packing_degree_le P hc hd v
  have hr := degree_sdiff_of_le (unionPieces_le G P) v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hGv hPv hr ⊢
  omega

/-- With no isolated vertices, failure of connectivity is a genuine even split. -/
lemma connected_of_positive_degree_no_split {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (hp : ∀ v, 0 < G.degree v) (hno : ¬HasEvenOneVertexSplit G) : G.Connected := by
  refine { preconnected := ?_, nonempty := inferInstance }
  intro a b
  by_contra hn
  let S : Set V := {x | G.Reachable a x}
  let A := RankBlocks.sideGraph G S
  let B := G \ A
  have hA : A ≤ G := fun _ _ h => h.1
  have hB : B ≤ G := sdiff_le
  have ha : A ≠ ⊥ := by
    obtain ⟨x,hx⟩ := (G.degree_pos_iff_exists_adj a).mp (hp a)
    have hh : A.Adj a x := ⟨hx,Reachable.refl _,hx.reachable⟩
    intro hbot
    simp only [hbot,bot_adj] at hh
  have hb : B ≠ ⊥ := by
    obtain ⟨x,hx⟩ := (G.degree_pos_iff_exists_adj b).mp (hp b)
    have hh : B.Adj b x := ⟨hx,fun h => hn h.2.1⟩
    intro hbot
    simp only [hbot,bot_adj] at hh
  have hab : Disjoint A.edgeSet B.edgeSet := by
    rw [show B = G \ A from rfl, edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet := by
    rw [show B = G \ A from rfl, edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hA)
  have hover : A.support ∩ B.support = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨y,hy⟩,⟨z,hz⟩⟩
    exact hz.2 ⟨hz.1,hy.2.1,hy.2.1.trans hz.1.reachable⟩
  exact hno ((hasEvenOneVertexSplit_iff G he).mpr
    ⟨A,B,hA,hB,ha,hb,hab,hcover,by simp [hover]⟩)

lemma IsVertexMinimal.small_packing_connected {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 0 < C)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ C) : (G \ unionPieces G P).Connected := by
  letI := hG.connected.nonempty
  apply connected_of_positive_degree_no_split _
    (by
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using even_residual_of_cycle_packing G hG.1 P hc hd v)
    (fun v => by
      have hh := hG.small_packing_degree_lower hC P hc hd hp v
      simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
      omega)
    (hG.small_packing_no_one_vertex_split P hc hd hp)

/-- Delete up to C cycle pieces, then any one vertex: all other vertices
remain mutually reachable. -/
lemma IsVertexMinimal.small_packing_delete_vertex_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 0 < C)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ C) {v a b : V} (ha : a ≠ v) (hb : b ≠ v) :
    ((G \ unionPieces G P).deleteIncidenceSet v).Reachable a b := by
  by_contra hn
  apply hG.small_packing_no_one_vertex_split P hc hd hp
  exact RankBlocks.split_of_deleted_unreachable
    (hG.small_packing_connected hC P hc hd hp)
    (by
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using even_residual_of_cycle_packing G hG.1 P hc hd v) ha hb hn

/-- A decomposition supplies at most one selected cycle per marked edge,
covering all marked edges that are present in the graph. -/
lemma exists_packing_cover_edges {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hd : IsDecomposition G D) (F : Set (Sym2 V)) :
    ∃ P : Finset G.Subgraph, P ⊆ D ∧ P.card ≤ F.ncard ∧
      G \ unionPieces G P ≤ G.deleteEdges F := by
  let P := D.filter (fun H => (H.edgeSet ∩ F).Nonempty)
  have hPD : P ⊆ D := Finset.filter_subset _ _
  have hex : ∀ H : {H // H ∈ P}, ∃ e, e ∈ H.val.edgeSet ∧ e ∈ F := by
    intro H
    exact (Finset.mem_filter.mp H.property).2
  choose f hf using hex
  let g : {H // H ∈ P} → F := fun H => ⟨f H,(hf H).2⟩
  have hi : Function.Injective g := by
    intro H K h
    apply Subtype.ext
    by_contra hHK
    have heq : f H = f K := congrArg Subtype.val h
    exact Set.disjoint_left.mp (hd.1 (hPD H.property) (hPD K.property) hHK)
      (hf H).1 (heq.symm ▸ (hf K).1)
  have hcard := Fintype.card_le_of_injective g hi
  have hPF : P.card ≤ F.ncard := by
    have hcP : Fintype.card {H // H ∈ P} = P.card := Fintype.card_coe P
    rw [hcP,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hcard
    exact hcard
  refine ⟨P,hPD,hPF,?_⟩
  intro a b hab
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hab.1,?_⟩
  intro heF
  have heG : s(a,b) ∈ G.edgeSet := hab.1
  rw [← hd.2] at heG
  obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp heG
  have hHP : H ∈ P := Finset.mem_filter.mpr ⟨hHD,s(a,b),heH,heF⟩
  apply hab.2
  change s(a,b) ∈ (unionPieces G P).edgeSet
  rw [unionPieces_edgeSet]
  exact Set.mem_iUnion₂.mpr ⟨H,hHP,heH⟩

/-- Simultaneously delete any vertex and at most C edges. The other vertices
remain connected. In particular deletion of a vertex cannot leave a bridge. -/
lemma IsVertexMinimal.vertex_and_edges_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 0 < C)
    (F : Set (Sym2 V)) (hF : F.ncard ≤ C) {v a b : V}
    (ha : a ≠ v) (hb : b ≠ v) :
    ((G.deleteIncidenceSet v).deleteEdges F).Reachable a b := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G hG.1
  obtain ⟨P,hPD,hPF,hres⟩ := exists_packing_cover_edges D hd F
  have hreach := hG.small_packing_delete_vertex_reachable hC P
    (fun H hH => hc H (hPD hH))
    (fun H hH K hK hne => hd.1 (hPD hH) (hPD hK) hne)
    (hPF.trans hF) ha hb
  apply hreach.mono
  intro x y hxy
  have hh := SimpleGraph.deleteIncidenceSet_adj.mp hxy
  have he := SimpleGraph.deleteEdges_adj.mp (hres hh.1)
  exact SimpleGraph.deleteEdges_adj.mpr
    ⟨SimpleGraph.deleteIncidenceSet_adj.mpr ⟨he.1,hh.2.1,hh.2.2⟩,he.2⟩

lemma IsVertexMinimal.deleted_vertex_edge_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 0 < C)
    {v a b : V} (ha : a ≠ v) (hb : b ≠ v) :
    (G.deleteIncidenceSet v).IsEdgeReachable (C+1) a b := by
  intro F hF
  apply hG.vertex_and_edges_reachable hC F ?_ ha hb
  have hh : F.ncard < C+1 := by
    rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card'] at hF
    exact_mod_cast hF
  omega

/-- A narrower, still unproved structural hypothesis would settle the original
conjecture. The packing need only make a vertex a separator; it need not
already disconnect the graph before that vertex is deleted. -/
lemma conjecture_of_small_packing_cut_vertex (C : ℕ) (hC : 0 < C)
    (hsep : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G.Connected → (∀ v, Even (G.degree v)) →
      (∀ v, 2*(C+2) ≤ G.degree v) → MinimalCounterexample.AllCyclesOptimal G →
      ∃ (P : Finset G.Subgraph) (v a b : V),
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
        P.card ≤ C ∧ a ≠ v ∧ b ≠ v ∧
        ¬((G \ unionPieces G P).deleteIncidenceSet v).Reachable a b) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_shifted_bound.mpr
  refine ⟨C,?_⟩
  intro V _ G he
  by_contra hb
  obtain ⟨W,instW,H,hH⟩ := exists_lex_minimal C G he hb
  letI := instW
  obtain ⟨P,v,a,b,hc,hd,hp,ha,hb,hn⟩ := hsep H hH.1.connected hH.1.1
    (hH.1.degree_lower hC) hH.allCyclesOptimal
  exact hn (hH.1.small_packing_delete_vertex_reachable hC P hc hd hp ha hb)

end Erdos184.ShiftedCritical
