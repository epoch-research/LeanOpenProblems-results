import Submission.OptimalSingletonForest

/-! Minimum-cardinality parity corrections, without any assertion that they
occur in an optimal cycle-and-edge decomposition. -/
open SimpleGraph
open scoped Classical symmDiff
namespace Erdos184Work.MinimumParity
set_option maxHeartbeats 800000
variable {V : Type*} [Fintype V]

def SameParity (F R : SimpleGraph V) : Prop :=
  ∀ v, Nat.card (F.neighborSet v) % 2 = Nat.card (R.neighborSet v) % 2

def Minimum (G F : SimpleGraph V) : Prop :=
  F ≤ G ∧ ∀ R ≤ G, SameParity R F → Nat.card F.edgeSet ≤ Nat.card R.edgeSet

lemma exists_minimum (G T : SimpleGraph V) (hTG : T ≤ G) :
    ∃ F, Minimum G F ∧ SameParity F T := by
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let S := Finset.univ.filter (fun F : SimpleGraph V => F ≤ G ∧ SameParity F T)
  have hS : S.Nonempty := ⟨T, by simp [S,hTG,SameParity]⟩
  obtain ⟨F,hF,hm⟩ := Finset.exists_min_image S (fun F => Nat.card F.edgeSet) hS
  have hf := (Finset.mem_filter.mp hF).2
  refine ⟨F,⟨hf.1,?_⟩,hf.2⟩
  intro R hRG hp
  exact hm R (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hRG,fun v => (hp v).trans (hf.2 v)⟩)

lemma symmDiff_sameParity (F C : SimpleGraph V)
    (he : ∀ v, Even (Nat.card (C.neighborSet v))) : SameParity (F ∆ C) F := by
  intro v
  have h := Vertex.degree_symmDiff_mod_two F C v
  have hc := Nat.even_iff.mp (he v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h
  omega

lemma symmDiff_card (F C : SimpleGraph V) :
    Nat.card (F ∆ C).edgeSet = Nat.card (F \ C).edgeSet + Nat.card (C \ F).edgeSet := by
  simp only [symmDiff_def, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sdiff,
    Nat.card_coe_set_eq]
  exact Set.ncard_union_eq (Set.disjoint_left.mpr (fun _ h₁ h₂ => h₁.2 h₂.1))

lemma sdiff_add_inf_card (F C : SimpleGraph V) :
    Nat.card (F \ C).edgeSet + Nat.card (F ⊓ C).edgeSet = Nat.card F.edgeSet := by
  have h := Finset.card_sdiff_add_card_inter F.edgeFinset C.edgeFinset
  simpa only [← SimpleGraph.edgeFinset_sdiff, ← SimpleGraph.edgeFinset_inf,
    SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h

/-- Flipping an even subgraph cannot remove more correction edges than it adds. -/
lemma Minimum.even_balance {G F : SimpleGraph V} (hm : Minimum G F)
    (C : SimpleGraph V) (hCG : C ≤ G)
    (he : ∀ v, Even (Nat.card (C.neighborSet v))) :
    Nat.card (F ⊓ C).edgeSet ≤ Nat.card (C \ F).edgeSet := by
  have hh := hm.2 (F ∆ C) (symmDiff_le_sup.trans (sup_le hm.1 hCG))
    (symmDiff_sameParity F C he)
  have hs := symmDiff_card F C
  have hc := sdiff_add_inf_card F C
  omega

lemma Minimum.acyclic {G F : SimpleGraph V} (hm : Minimum G F) : F.IsAcyclic := by
  intro v p hp
  have hC : p.toSubgraph.spanningCoe ≤ F := p.toSubgraph.spanningCoe_le
  have he : ∀ w, Even (Nat.card (p.toSubgraph.spanningCoe.neighborSet w)) := by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycle_spanning_even F hp w
  have hb := hm.even_balance p.toSubgraph.spanningCoe (hC.trans hm.1) he
  rw [inf_eq_right.mpr hC, sdiff_eq_bot_iff.mpr hC] at hb
  have hc := cycle_edge_count F hp
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc
  have hz : Nat.card (⊥ : SimpleGraph V).edgeSet = 0 := by simp
  rw [hz] at hb
  change Nat.card p.toSubgraph.edgeSet ≤ 0 at hb
  change Nat.card p.toSubgraph.edgeSet = p.length at hc
  have hl := hp.three_le_length
  omega

lemma Minimum.no_one_edge_cycle {G F : SimpleGraph V} (hm : Minimum G F)
    {a b z : V} (p : G.Walk z z) (hp : p.IsCycle)
    (hab : (G \ F).Adj a b)
    (hi : (G \ F) ⊓ p.toSubgraph.spanningCoe = SimpleGraph.edge a b) : False := by
  let C := p.toSubgraph.spanningCoe
  have hCG : C ≤ G := p.toSubgraph.spanningCoe_le
  have hCM : C \ F = SimpleGraph.edge a b := by
    rw [← hi]
    ext x y
    exact ⟨fun h => ⟨⟨hCG h.1,h.2⟩,h.1⟩,fun h => ⟨h.2,h.1.2⟩⟩
  have he : ∀ w, Even (Nat.card (C.neighborSet w)) := by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycle_spanning_even G hp w
  have hb := hm.even_balance C hCG he
  have hs := sdiff_add_inf_card C F
  rw [inf_comm C F] at hs
  have hone : Nat.card (C \ F).edgeSet = 1 := by
    rw [hCM,SimpleGraph.edge_edgeSet_of_ne hab.ne]
    simp
  have hc := cycle_edge_count G hp
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc
  change Nat.card C.edgeSet = p.length at hc
  have hl := hp.three_le_length
  omega

lemma Minimum.reachable_induced {G F : SimpleGraph V} (hm : Minimum G F)
    {a b : V} (hr : F.Reachable a b) (hab : G.Adj a b) : F.Adj a b := by
  by_contra hf
  let M := SimpleGraph.edge a b
  let T := F ⊔ M
  have hmab : M.Adj a b := (SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩
  have ht : T.Adj a b := Or.inr hmab
  have hTG : T ≤ G := sup_le hm.1 ((SimpleGraph.edge_le_iff G).mpr (Or.inr hab))
  have hdel : T.deleteEdges {s(a,b)} = F := by
    ext x y
    have hM : M.edgeSet = {s(a,b)} := SimpleGraph.edge_edgeSet_of_ne hab.ne
    have hmxy : M.Adj x y ↔ s(x,y) = s(a,b) := by
      change s(x,y) ∈ M.edgeSet ↔ _
      rw [hM]
      rfl
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
    exact hnot (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mpr ⟨ht,h⟩)
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
  exact hm.no_one_edge_cycle q hq ⟨hab,hf⟩ hi

/-- Every finite preconnected graph of even order has a spanning odd forest
whose components are induced in the host (a perfect forest). -/
lemma exists_perfect_forest (G : SimpleGraph V) (hc : G.Preconnected)
    (hn : Even (Fintype.card V)) :
    ∃ F, Minimum G F ∧ F.IsAcyclic ∧
      (∀ v, Odd (Nat.card (F.neighborSet v))) ∧
      (∀ a b, F.Reachable a b → G.Adj a b → F.Adj a b) := by
  obtain ⟨T,hTG,hT⟩ := Vertex.exists_parity_subgraph hc Finset.univ (by simpa using hn)
  obtain ⟨F,hm,hp⟩ := exists_minimum G T hTG
  refine ⟨F,hm,hm.acyclic,?_,fun _ _ hr ha => hm.reachable_induced hr ha⟩
  intro v
  have ht := hT v
  simp only [Finset.mem_univ,ite_true,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at ht
  rw [Nat.odd_iff,hp v,ht]

end Erdos184Work.MinimumParity
#print axioms Erdos184Work.MinimumParity.exists_minimum
#print axioms Erdos184Work.MinimumParity.Minimum.even_balance
#print axioms Erdos184Work.MinimumParity.Minimum.acyclic
#print axioms Erdos184Work.MinimumParity.Minimum.reachable_induced
