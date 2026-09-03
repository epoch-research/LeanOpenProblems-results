import Submission.MinimalSingletons
import Submission.CycleForestCertificate

/-! Cycle exchange for a secondary-optimal singleton forest.
This module does not establish the original uniform bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingletonExchange
open Critical MaximumCycles Subfamilies
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V]

lemma disjoint_sup_even {A B : SimpleGraph V} (hd : Disjoint A B)
    (he : ∀ v, Even ((A ⊔ B).degree v)) (ha : ∀ v, Even (A.degree v)) :
    ∀ v, Even (B.degree v) := by
  intro v
  have h := Vertex.degree_sup_inf A B v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h
  rw [disjoint_iff.mp hd] at h
  have hb : (⊥ : SimpleGraph V).degree v = 0 := by simp
  have he' := Nat.even_iff.mp (he v)
  have ha' := Nat.even_iff.mp (ha v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hb he' ha' ⊢
  rw [Nat.even_iff]
  omega

lemma swap_even {E C M : SimpleGraph V} (hME : M ≤ E) (hMC : M ≤ C)
    (hinter : E ⊓ C = M) (hE : ∀ v, Even (E.degree v))
    (hC : ∀ v, Even (C.degree v)) :
    ∀ v, Even (((E \ M) ⊔ (C \ M)).degree v) := by
  have hd : Disjoint (E \ M) (C \ M) := by
    rw [disjoint_iff]
    ext x y
    constructor
    · rintro ⟨⟨he,hm⟩,hc⟩
      exact hm (show M.Adj x y from hinter ▸ (show (E ⊓ C).Adj x y from ⟨he,hc.1⟩))
    · exact False.elim
  intro v
  have he := degree_sdiff_add E M hME v
  have hc := degree_sdiff_add C M hMC v
  have hs := Vertex.degree_sup_inf (E \ M) (C \ M) v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hs
  rw [disjoint_iff.mp hd] at hs
  have hb : (⊥ : SimpleGraph V).degree v = 0 := by simp
  have he' := Nat.even_iff.mp (hE v)
  have hc' := Nat.even_iff.mp (hC v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he hc hs hb he' hc' ⊢
  rw [Nat.even_iff]
  omega

/-- Replacing one edge of an even graph by the remaining edges of a cycle
costs at most the length of that replacement minus one. -/
lemma cycle_exchange_bound {E T : SimpleGraph V} (hE : ∀ v, Even (E.degree v))
    {a b z : V} (p : T.Walk z z) (hp : p.IsCycle)
    (hab : E.Adj a b) (heC : p.toSubgraph.Adj a b)
    (hinter : E ⊓ p.toSubgraph.spanningCoe = SimpleGraph.edge a b) :
    number ((E \ SimpleGraph.edge a b) ⊔
      (p.toSubgraph.spanningCoe \ SimpleGraph.edge a b)) + 1 ≤
      number E + (p.toSubgraph.spanningCoe \ SimpleGraph.edge a b).edgeFinset.card := by
  let M := SimpleGraph.edge a b
  let C := p.toSubgraph.spanningCoe
  have hME : M ≤ E := (SimpleGraph.edge_le_iff E).mpr (Or.inr hab)
  have hMC : M ≤ C := (SimpleGraph.edge_le_iff C).mpr (Or.inr heC)
  obtain ⟨D,hD,hdec,hcard⟩ := Rigidity.minimum_cycles hE
  have heD : s(a,b) ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ hab
  obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp heD
  let K := H.spanningCoe
  let R := E \ K
  let S := (K \ M) ⊔ (C \ M)
  have hMK : M ≤ K := (SimpleGraph.edge_le_iff K).mpr (Or.inr heH)
  have hKE : K ≤ E := H.spanningCoe_le
  have hKC : K ⊓ C = M := by
    apply le_antisymm
    · exact (inf_le_inf_right C hKE).trans hinter.le
    · exact le_inf hMK hMC
  have hK : ∀ v, Even (K.degree v) := regular_two_spanning_even H (hD H hHD).2
  have hC : ∀ v, Even (C.degree v) := regular_two_spanning_even p.toSubgraph (cycle_coe_regular T hp).2
  have hS := swap_even hMK hMC hKC hK hC
  have hdel : K \ M = K.deleteEdges {s(a,b)} := by
    ext x y
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff]
    have hm : M.edgeSet = {s(a,b)} := SimpleGraph.edge_edgeSet_of_ne hab.ne
    have hh : M.Adj x y ↔ s(x,y) = s(a,b) := by change s(x,y) ∈ M.edgeSet ↔ _; rw [hm]; rfl
    rw [hh]
  have hacyc : (K \ M).IsAcyclic := by
    rw [hdel]
    exact SingleAddition.delete_cycle_edge_acyclic H (hD H hHD).1 (hD H hHD).2 ⟨s(a,b),heH⟩
  obtain ⟨A,hA,hdecA,hcountA⟩ := SingleAddition.even_feedback_decomposition S (K \ M) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hS) hacyc
  have hcost : number S ≤ (C \ M).edgeFinset.card := by
    have hn := number_le A (fun J hJ => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hA J hJ)) hdecA
    have hle : S \ (K \ M) ≤ C \ M := by
      intro x y hxy
      exact hxy.1.elim (fun hk => (hxy.2 hk).elim) id
    have hc := Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcountA hc ⊢
    omega
  have hdis : Disjoint R.edgeSet S.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hs
    change e ∈ (E \ K).edgeSet at he
    rw [SimpleGraph.edgeSet_sdiff] at he
    change e ∈ ((K \ M) ⊔ (C \ M)).edgeSet at hs
    rw [SimpleGraph.edgeSet_sup,SimpleGraph.edgeSet_sdiff,SimpleGraph.edgeSet_sdiff] at hs
    rcases hs with hk | hc
    · exact he.2 hk.1
    · have hm : e ∈ M.edgeSet := by
        change e ∈ (SimpleGraph.edge a b).edgeSet
        rw [← hinter,SimpleGraph.edgeSet_inf]
        exact ⟨he.1,hc.1⟩
      exact hc.2 hm
  have hnum := CycleForestCertificate.number_sup_le hdis
  have hsup : R ⊔ S = (E \ M) ⊔ (C \ M) := by
    ext x y
    simp only [R,S,SimpleGraph.sup_adj,SimpleGraph.sdiff_adj]
    constructor
    · rintro (⟨he,hk⟩ | ⟨hk,hm⟩ | hc)
      · exact Or.inl ⟨he,fun hm => hk (hMK hm)⟩
      · exact Or.inl ⟨hKE hk,hm⟩
      · exact Or.inr hc
    · rintro (⟨he,hm⟩ | hc)
      · by_cases hk : K.Adj x y
        · exact Or.inr (Or.inl ⟨hk,hm⟩)
        · exact Or.inl ⟨he,hk⟩
      · exact Or.inr (Or.inr hc)
  have hRnum : number R + 1 = number E := by
    have hD' : ∀ J ∈ D, IsCycleOrEdge J.coe := fun J hJ => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD J hJ)
    have h := minimal_subfamily_number D hD' hdec hcard (D.erase H) (Finset.erase_subset _ _)
    have hRgraph : subfamilyGraph (D.erase H) = R := by
      ext x y
      constructor
      · intro hxy
        have he : s(x,y) ∈ ⋃ J ∈ D.erase H, J.edgeSet := (subfamilyGraph_edges _).symm ▸ hxy
        obtain ⟨J,hJ,heJ⟩ := Set.mem_iUnion₂.mp he
        refine ⟨J.adj_sub heJ,?_⟩
        intro heH'
        exact Set.disjoint_left.mp (hdec.1 (Finset.mem_erase.mp hJ).2 hHD (Finset.mem_erase.mp hJ).1) heJ heH'
      · rintro ⟨he,hk⟩
        have heD : s(x,y) ∈ ⋃ J ∈ D, J.edgeSet := hdec.2.symm ▸ he
        obtain ⟨J,hJD,heJ⟩ := Set.mem_iUnion₂.mp heD
        have hne : J ≠ H := by rintro rfl; exact hk heJ
        change s(x,y) ∈ (subfamilyGraph (D.erase H)).edgeSet
        rw [subfamilyGraph_edges]
        exact Set.mem_iUnion₂.mpr ⟨J,Finset.mem_erase.mpr ⟨hne,hJD⟩,heJ⟩
    rw [hRgraph] at h
    have hc := Finset.card_erase_add_one hHD
    omega
  rw [hsup] at hnum
  change number ((E \ M) ⊔ (C \ M)) + 1 ≤ number E + (C \ M).edgeFinset.card
  omega

end Erdos184Work.SingletonExchange
#print axioms Erdos184Work.SingletonExchange.cycle_exchange_bound
