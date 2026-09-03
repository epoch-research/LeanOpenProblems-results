import Submission.SeparateTwoEdges

/-! A five-spoke reduction with an explicit two-shortcut collision alternative.
A smallest odd-order failure forces a saturated proxy and forces the two
shortcut edges into the same member of every budget-sized proxy partition. -/
namespace Erdos583FiveSpokeReductionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583SharedExpansionDevelopment Erdos583PairedSuppressionDevelopment
open Erdos583SeparateTwoEdgesDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*}

lemma two_shortcuts_ne (a b : Fin 2 → V)
    (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set V) {a j,b j})) :
    s(a 0,b 0) ≠ s(a 1,b 1) := by
  intro h
  have hd := hpairs (by decide : (0 : Fin 2) ≠ 1)
  rcases Sym2.eq_iff.mp h with ⟨h1,_⟩|⟨h1,_⟩
  · exact Set.disjoint_left.mp hd (Or.inl rfl) (Or.inl h1)
  · exact Set.disjoint_left.mp hd (Or.inl rfl) (Or.inr h1)

lemma two_edge_function (a b : Fin 2 → V) :
    (fun i ↦ s(a i,b i))=![s(a 0,b 0),s(a 1,b 1)] := by
  funext i
  fin_cases i <;> rfl

lemma restore_five_spokes [Fintype V] (G : SimpleGraph V) (r z : V) (hz : G.Adj r z) (a b : Fin 2 → V)
    (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i)) (hab : ∀ i, a i ≠ b i)
    (haz : ∀ i, a i ≠ z) (hbz : ∀ i, b i ≠ z)
    (hfresh : ∀ i, ¬G.Adj (a i) (b i))
    (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set V) {a j,b j}))
    (hN : ∀ x, G.Adj r x → x=z ∨ ∃ i, x=a i ∨ x=b i)
    (D : Finset (proxy (G.deleteEdges {s(r,z)}) r a b).Subgraph)
    (hD : GoodDecomposition (proxy (G.deleteEdges {s(r,z)}) r a b) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+2 := by
  obtain ⟨E,hE,hEc,hsep⟩ := separate_two_edges D hD (s(a 0,b 0)) (s(a 1,b 1)) (two_shortcuts_ne a b hpairs)
  have hs : Separated E (fun i ↦ s(a i,b i)) := by rwa [two_edge_function]
  obtain ⟨F,hF,hFc⟩ := restore_pairs_and_edge G r z hz a b ha hb hab haz hbz hfresh hpairs hN E hE hs
  exact ⟨F,hF,by omega⟩

lemma proxy_connected_of_induce {I : Type*} (G : SimpleGraph V) (r : V) (a b : I → V)
    (ha : ∀ i, a i ≠ r) (hb : ∀ i, b i ≠ r)
    (hc : (G.induce ({r}ᶜ : Set V)).Connected) : SupportConnected (proxy G r a b) := by
  have hr := proxy_avoids G r a b ha hb
  let f : (G.induce ({r}ᶜ : Set V)) →g within G ({r}ᶜ : Set V) :=
    { toFun := Subtype.val, map_rel' := by intro x y hxy; exact ⟨hxy,x.property,y.property⟩ }
  intro x hx y hy
  have hxr : x ≠ r := fun h ↦ hr (h ▸ hx)
  have hyr : y ≠ r := fun h ↦ hr (h ▸ hy)
  obtain ⟨P⟩ := hc ⟨x,hxr⟩ ⟨y,hyr⟩
  exact (P.map f).reachable.mono le_sup_left

lemma within_delete_center_edge (G : SimpleGraph V) (r z : V) :
    within (G.deleteEdges {s(r,z)}) ({r}ᶜ : Set V)=within G ({r}ᶜ : Set V) := by
  ext x y
  constructor
  · rintro ⟨hxy,hx,hy⟩
    exact ⟨(G.deleteEdges_le _) hxy,hx,hy⟩
  · rintro ⟨hxy,hx,hy⟩
    refine ⟨deleteEdges_adj.mpr ⟨hxy,?_⟩,hx,hy⟩
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h,_⟩|⟨_,h⟩
    · exact hx h
    · exact hy h

lemma proxy_delete_center_edge {I : Type*} (G : SimpleGraph V) (r z : V) (a b : I → V) :
    proxy (G.deleteEdges {s(r,z)}) r a b=proxy G r a b := by
  rw [proxy,proxy,within_delete_center_edge]

section Failure
variable {n : ℕ} (hn : Odd n) {G : SimpleGraph (Fin n)}
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (r z : Fin n) (hz : G.Adj r z) (a b : Fin 2 → Fin n)
  (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i)) (hab : ∀ i, a i ≠ b i)
  (haz : ∀ i, a i ≠ z) (hbz : ∀ i, b i ≠ z)
  (hfresh : ∀ i, ¬G.Adj (a i) (b i))
  (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set (Fin n)) {a j,b j}))
  (hN : ∀ x, G.Adj r x → x=z ∨ ∃ i, x=a i ∨ x=b i)
include hn hfail hz ha hb hab haz hbz hfresh hpairs hN

lemma failure_proxy_minimum (D : Finset (proxy (G.deleteEdges {s(r,z)}) r a b).Subgraph)
    (hD : GoodDecomposition (proxy (G.deleteEdges {s(r,z)}) r a b) D) :
    ⌈((n-1 : ℕ) : ℚ)/2⌉₊ ≤ D.card := by
  by_contra hlt
  obtain ⟨E,hE,hEc⟩ := restore_five_spokes G r z hz a b ha hb hab haz hbz hfresh hpairs hN D hD
  apply hfail
  refine ⟨E,hE,?_⟩
  simp only [Fintype.card_fin,ceil_half] at hlt ⊢
  obtain ⟨m,hm⟩ := hn
  omega

lemma failure_proxy_same_owner (D : Finset (proxy (G.deleteEdges {s(r,z)}) r a b).Subgraph)
    (hD : GoodDecomposition (proxy (G.deleteEdges {s(r,z)}) r a b) D)
    (hDc : D.card ≤ ⌈((n-1 : ℕ) : ℚ)/2⌉₊) :
    ∃ K ∈ D, s(a 0,b 0) ∈ K.edgeSet ∧ s(a 1,b 1) ∈ K.edgeSet := by
  by_contra hno
  have hs : Separated D (fun i ↦ s(a i,b i)) := by
    rw [two_edge_function]
    exact (two_separated_iff D _ _).mpr (fun K hK hh ↦ hno ⟨K,hK,hh⟩)
  obtain ⟨E,hE,hEc⟩ := restore_pairs_and_edge G r z hz a b ha hb hab haz hbz hfresh hpairs hN D hD hs
  apply hfail
  refine ⟨E,hE,?_⟩
  simp only [Fintype.card_fin,ceil_half] at hDc ⊢
  obtain ⟨m,hm⟩ := hn
  omega

lemma failure_proxy_certificate (hsmall : VertexCritical.SmallerOrders n) (hG : G.Connected) :
    ∃ D : Finset (proxy (G.deleteEdges {s(r,z)}) r a b).Subgraph,
      GoodDecomposition (proxy (G.deleteEdges {s(r,z)}) r a b) D ∧
      D.card=⌈((n-1 : ℕ) : ℚ)/2⌉₊ ∧
      (∃ K ∈ D, s(a 0,b 0) ∈ K.edgeSet ∧ s(a 1,b 1) ∈ K.edgeSet) ∧
      ∀ E : Finset (proxy (G.deleteEdges {s(r,z)}) r a b).Subgraph,
        GoodDecomposition (proxy (G.deleteEdges {s(r,z)}) r a b) E →
        ⌈((n-1 : ℕ) : ℚ)/2⌉₊ ≤ E.card := by
  have hc := CutVertexReduction.delete_vertex_connected_of_odd_failure hsmall hn hG hfail r
  have hcJ : SupportConnected (proxy (G.deleteEdges {s(r,z)}) r a b) := by
    rw [proxy_delete_center_edge]
    exact proxy_connected_of_induce G r a b (fun i ↦ (ha i).ne.symm) (fun i ↦ (hb i).ne.symm) hc
  obtain ⟨D,hD,hDc⟩ := proxy_partition hsmall (G.deleteEdges {s(r,z)}) r a b
    (fun i ↦ (ha i).ne.symm) (fun i ↦ (hb i).ne.symm) hcJ
  have hlow := failure_proxy_minimum hn hfail r z hz a b ha hb hab haz hbz hfresh hpairs hN
  refine ⟨D,hD,le_antisymm hDc (hlow D hD),?_,hlow⟩
  exact failure_proxy_same_owner hn hfail r z hz a b ha hb hab haz hbz hfresh hpairs hN D hD hDc

end Failure
end Erdos583FiveSpokeReductionDevelopment
