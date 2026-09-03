import Submission.SingletonCycleExchange

/-! A secondary-optimal singleton forest has induced connected components.
This structural exchange is not a proof of the original uniform bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingletonExchange
open Critical MaximumCycles Subfamilies
set_option maxHeartbeats 1600000

variable {V : Type*} [Fintype V]

/-- An optimal split into an even graph and singleton edges. -/
def Optimal (G F : SimpleGraph V) : Prop :=
  F ≤ G ∧ (∀ v, Even (Nat.card ((G \ F).neighborSet v))) ∧
    number (G \ F) + Nat.card F.edgeSet = number G

/-- Minimize the singleton count among all optimal splits. -/
def Best (G F : SimpleGraph V) : Prop :=
  Optimal G F ∧ ∀ R, Optimal G R → Nat.card F.edgeSet ≤ Nat.card R.edgeSet

lemma split_lower_bound {G F : SimpleGraph V} (hF : F ≤ G) :
    number G ≤ number (G \ F) + Nat.card F.edgeSet := by
  have hd : Disjoint (G \ F).edgeSet F.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]; exact Set.disjoint_sdiff_left
  have hn := CycleForestCertificate.number_sup_le hd
  rw [sdiff_sup_cancel hF] at hn
  have he := number_le_edges F
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at he
  omega

lemma exists_optimal (G : SimpleGraph V) : ∃ F, Optimal G F := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
  let A := edgePieces D
  let C := D \ A
  let F := subfamilyGraph A
  let E := subfamilyGraph C
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have hCD : C ⊆ D := Finset.sdiff_subset
  have hC : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases hD H (hCD hH) with hc | he
    · simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc
    · exact ((Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mpr ⟨hCD hH,he⟩)).elim
  have hE : ∀ v, Even (E.degree v) := cycle_subfamily_even C hC
    (fun _ hH _ hK hne => hdec.1 (hCD hH) (hCD hK) hne)
  have hEF : E = G \ F := by
    ext x y
    constructor
    · intro hxy
      have hh : s(x,y) ∈ ⋃ H ∈ C, H.edgeSet := (subfamilyGraph_edges C).symm ▸ hxy
      obtain ⟨H,hHC,heH⟩ := Set.mem_iUnion₂.mp hh
      refine ⟨H.adj_sub heH,?_⟩
      intro hf
      have hh : s(x,y) ∈ ⋃ K ∈ A, K.edgeSet := (subfamilyGraph_edges A).symm ▸ hf
      obtain ⟨K,hKA,heK⟩ := Set.mem_iUnion₂.mp hh
      have hne : H ≠ K := fun heq => (Finset.mem_sdiff.mp hHC).2 (heq ▸ hKA)
      exact Set.disjoint_left.mp (hdec.1 (hCD hHC) (hAD hKA) hne) heH heK
    · rintro ⟨hxy,hf⟩
      have hh : s(x,y) ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ hxy
      obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp hh
      have hn : H ∉ A := by
        intro hHA
        apply hf
        change s(x,y) ∈ (subfamilyGraph A).edgeSet
        rw [subfamilyGraph_edges]
        exact Set.mem_iUnion₂.mpr ⟨H,hHA,heH⟩
      change s(x,y) ∈ (subfamilyGraph C).edgeSet
      rw [subfamilyGraph_edges]
      exact Set.mem_iUnion₂.mpr ⟨H,Finset.mem_sdiff.mpr ⟨hHD,hn⟩,heH⟩
  have hn := minimal_subfamily_number D hD hdec hcard C hCD
  have hf := edgePieces_graph_card D hdec
  have hs := Finset.card_sdiff_add_card_eq_card hAD
  change number E = C.card at hn
  change F.edgeFinset.card = A.card at hf
  change C.card + A.card = D.card at hs
  refine ⟨F,subfamilyGraph_le A,?_,?_⟩
  · intro v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hE
    rw [← hEF]
    exact hE v
  · rw [← hEF,hn]
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hf
    omega

lemma exists_best (G : SimpleGraph V) : ∃ F, Best G F := by
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let S := Finset.univ.filter (Optimal G)
  obtain ⟨R,hR⟩ := exists_optimal G
  have hs : S.Nonempty := ⟨R,by simp [S,hR]⟩
  obtain ⟨F,hF,hm⟩ := Finset.exists_min_image S (fun F => Nat.card F.edgeSet) hs
  refine ⟨F,(Finset.mem_filter.mp hF).2,?_⟩
  intro R hR
  exact hm R (by simp [S,hR])

lemma Optimal.acyclic {G F : SimpleGraph V} (h : Optimal G F) : F.IsAcyclic := by
  by_contra ha
  have hn := number_lt_edges_of_cycle F ha
  have hd : Disjoint (G \ F).edgeSet F.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]; exact Set.disjoint_sdiff_left
  have hb := CycleForestCertificate.number_sup_le hd
  rw [sdiff_sup_cancel h.1] at hb
  have he := h.2.2
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hn
  omega

/-- A cycle cannot have exactly one edge outside a secondary-optimal singleton forest. -/
lemma Best.no_one_edge_cycle {G F : SimpleGraph V} (hbest : Best G F)
    {a b z : V} (p : G.Walk z z) (hp : p.IsCycle)
    (hab : (G \ F).Adj a b) (heC : p.toSubgraph.Adj a b)
    (hinter : (G \ F) ⊓ p.toSubgraph.spanningCoe = SimpleGraph.edge a b) : False := by
  let E := G \ F
  let C := p.toSubgraph.spanningCoe
  let M := SimpleGraph.edge a b
  let R := C \ M
  let F' := (F \ R) ⊔ M
  let E' := (E \ M) ⊔ R
  have hF := hbest.1.1
  have hCG : C ≤ G := p.toSubgraph.spanningCoe_le
  have hME : M ≤ E := (SimpleGraph.edge_le_iff E).mpr (Or.inr hab)
  have hMC : M ≤ C := (SimpleGraph.edge_le_iff C).mpr (Or.inr heC)
  have hMF : Disjoint M F := by
    rw [disjoint_iff]
    ext x y
    exact ⟨fun h => (hME h.1).2 h.2,False.elim⟩
  have hRF : R ≤ F := by
    intro x y hxy
    by_contra hf
    have hm : M.Adj x y := by
      change (SimpleGraph.edge a b).Adj x y
      rw [← hinter]
      exact ⟨⟨hCG hxy.1,hf⟩,hxy.1⟩
    exact hxy.2 hm
  have hF'G : F' ≤ G := sup_le (sdiff_le.trans hF) (hME.trans sdiff_le)
  have hE' : G \ F' = E' := by
    ext x y
    simp only [F',E',E,SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
    constructor
    · rintro ⟨hg,hn⟩
      by_cases hf : F.Adj x y
      · by_cases hr : R.Adj x y
        · exact Or.inr hr
        · exact (hn (Or.inl ⟨hf,hr⟩)).elim
      · exact Or.inl ⟨⟨hg,hf⟩,fun hm => hn (Or.inr hm)⟩
    · rintro (⟨⟨hg,hf⟩,hm⟩ | hr)
      · exact ⟨hg,fun h => h.elim (fun h => hf h.1) hm⟩
      · refine ⟨hCG hr.1,?_⟩
        rintro (⟨_,hn⟩ | hm)
        · exact hn hr
        · exact hr.2 hm
  have hEe : ∀ v, Even (E.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hbest.1.2.1
  have hCe : ∀ v, Even (C.degree v) := regular_two_spanning_even p.toSubgraph (cycle_coe_regular G hp).2
  have hE'e := swap_even (E := E) (C := C) (M := M) hME hMC hinter
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hEe)
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hCe)
  have hcost := cycle_exchange_bound (E := E) (T := G)
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hEe)
    p hp hab heC hinter
  change number E' + 1 ≤ number E + R.edgeFinset.card at hcost
  have hMcard : Nat.card M.edgeSet = 1 := by
    change Nat.card (SimpleGraph.edge a b).edgeSet = 1
    rw [SimpleGraph.edge_edgeSet_of_ne hab.ne]
    simp
  have hRcard : Nat.card R.edgeSet + 1 = p.length := by
    have hs : R.edgeFinset.card + M.edgeFinset.card = C.edgeFinset.card := by
      change (C \ M).edgeFinset.card + M.edgeFinset.card = C.edgeFinset.card
      rw [SimpleGraph.edgeFinset_sdiff]
      exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hMC)
    have hc := cycle_edge_count G hp
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hs hc
    change Nat.card C.edgeSet = p.length at hc
    omega
  have hF'card : Nat.card F'.edgeSet + Nat.card R.edgeSet = Nat.card F.edgeSet + 1 := by
    have hs : (F \ R).edgeFinset.card + R.edgeFinset.card = F.edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_sdiff]
      exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hRF)
    have hd : Disjoint (F \ R).edgeFinset M.edgeFinset := by
      apply Finset.disjoint_left.mpr
      intro e he hm
      have heF := SimpleGraph.edgeFinset_mono (show F \ R ≤ F from sdiff_le) he
      exact Set.disjoint_left.mp (SimpleGraph.disjoint_edgeSet.mpr hMF)
        (SimpleGraph.mem_edgeFinset.mp hm) (SimpleGraph.mem_edgeFinset.mp heF)
    have hu : F'.edgeFinset.card = (F \ R).edgeFinset.card + M.edgeFinset.card := by
      change ((F \ R) ⊔ M).edgeFinset.card = (F \ R).edgeFinset.card + M.edgeFinset.card
      rw [SimpleGraph.edgeFinset_sup,Finset.card_union_of_disjoint hd]
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hs hu
    omega
  have hopt : Optimal G F' := by
    refine ⟨hF'G,?_,?_⟩
    · intro v
      rw [hE']
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hE'e v
    · have hlo := split_lower_bound hF'G
      rw [hE'] at hlo ⊢
      have he := hbest.1.2.2
      change number E + Nat.card F.edgeSet = number G at he
      simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcost
      omega
  have hmin := hbest.2 F' hopt
  have hlen := hp.three_le_length
  omega

lemma Best.reachable_induced {G F : SimpleGraph V} (hbest : Best G F)
    {a b : V} (hr : F.Reachable a b) (hab : G.Adj a b) : F.Adj a b := by
  by_contra hf
  let M := SimpleGraph.edge a b
  let T := F ⊔ M
  have hm : M.Adj a b := (SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩
  have ht : T.Adj a b := Or.inr hm
  have hTG : T ≤ G := sup_le hbest.1.1 ((SimpleGraph.edge_le_iff G).mpr (Or.inr hab))
  have hdel : T.deleteEdges {s(a,b)} = F := by
    ext x y
    have hM : M.edgeSet = {s(a,b)} := SimpleGraph.edge_edgeSet_of_ne hab.ne
    have hmxy : M.Adj x y ↔ s(x,y) = s(a,b) := by change s(x,y) ∈ M.edgeSet ↔ _; rw [hM]; rfl
    simp only [T,SimpleGraph.deleteEdges_adj,SimpleGraph.sup_adj,Set.mem_singleton_iff,hmxy]
    constructor
    · rintro ⟨h,hn⟩
      exact h.elim id (fun hh => (hn hh).elim)
    · intro hxy
      refine ⟨Or.inl hxy,?_⟩
      intro he
      apply hf
      change s(a,b) ∈ F.edgeSet
      rw [← he]
      exact hxy
  have hnot : ¬ T.IsBridge s(a,b) := by
    intro hb
    have hh := (SimpleGraph.isBridge_iff.mp hb).2
    change ¬ (T.deleteEdges {s(a,b)}).Reachable a b at hh
    rw [hdel] at hh
    exact hh hr
  have hex : ∃ (z : V) (p : T.Walk z z), p.IsCycle ∧ s(a,b) ∈ p.edges := by
    by_contra! h
    apply hnot
    exact SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mpr ⟨ht,h⟩
  obtain ⟨z,p,hp,he⟩ := hex
  let q := p.mapLe hTG
  have hq : q.IsCycle := hp.mapLe hTG
  have hqe : q.toSubgraph.Adj a b := by
    exact (Walk.adj_toSubgraph_mapLe hTG).mpr (p.mem_edges_toSubgraph.mpr he)
  have hi : (G \ F) ⊓ q.toSubgraph.spanningCoe = M := by
    apply le_antisymm
    · intro x y hxy
      have hp' : p.toSubgraph.Adj x y := (Walk.adj_toSubgraph_mapLe hTG).mp hxy.2
      exact (p.toSubgraph.adj_sub hp').elim (fun hF => (hxy.1.2 hF).elim) id
    · exact le_inf ((SimpleGraph.edge_le_iff (G \ F)).mpr (Or.inr ⟨hab,hf⟩))
        ((SimpleGraph.edge_le_iff q.toSubgraph.spanningCoe).mpr (Or.inr hqe))
  exact hbest.no_one_edge_cycle q hq ⟨hab,hf⟩ hqe hi

end Erdos184Work.SingletonExchange
#print axioms Erdos184Work.SingletonExchange.exists_best
#print axioms Erdos184Work.SingletonExchange.Best.reachable_induced
