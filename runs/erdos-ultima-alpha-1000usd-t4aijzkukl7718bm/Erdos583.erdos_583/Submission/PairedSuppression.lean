import Submission.SharedExpansion

/-! Pairing the spokes at a vertex gives a valid reduction when the shortcut
edges are separated by the inductive path partition. No existence theorem for
such a separated partition is assumed here. -/
namespace Erdos583PairedSuppressionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583SharedExpansionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
variable {V I : Type*}

noncomputable def pairGraph (a b : I → V) : SimpleGraph V := ⨆ i, edge (a i) (b i)

lemma pairGraph_adj (a b : I → V) (x y : V) :
    (pairGraph a b).Adj x y ↔ ∃ i, (edge (a i) (b i)).Adj x y := iSup_adj

lemma pairGraph_edges (a b : I → V) (hab : ∀ i, a i ≠ b i) :
    (pairGraph a b).edgeSet=Set.range (fun i ↦ s(a i,b i)) := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    change (pairGraph a b).Adj x y ↔ ∃ i, s(a i,b i)=s(x,y)
    rw [pairGraph_adj]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨i,?_⟩
      rcases (edge_adj _ _ _ _).mp hi with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
      · rw [h1,h2]
      · rw [h1,h2]; exact Sym2.eq_swap
    · rintro ⟨i,hi⟩
      refine ⟨i,(edge_adj _ _ _ _).mpr ?_⟩
      rcases Sym2.eq_iff.mp hi with ⟨h1,h2⟩|⟨h1,h2⟩
      · exact ⟨Or.inl ⟨h1.symm,h2.symm⟩,by simpa only [←h1,←h2] using hab i⟩
      · exact ⟨Or.inr ⟨h2.symm,h1.symm⟩,by simpa only [←h1,←h2] using (hab i).symm⟩

noncomputable def proxy (G : SimpleGraph V) (r : V) (a b : I → V) : SimpleGraph V :=
  within G ({r}ᶜ : Set V) ⊔ pairGraph a b

lemma proxy_pair_adj (G : SimpleGraph V) (r : V) (a b : I → V) (hab : ∀ i, a i ≠ b i) (i : I) :
    (proxy G r a b).Adj (a i) (b i) :=
  Or.inr ((pairGraph_adj a b _ _).mpr ⟨i,(edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab i⟩⟩)

lemma proxy_avoids (G : SimpleGraph V) (r : V) (a b : I → V)
    (ha : ∀ i, a i ≠ r) (hb : ∀ i, b i ≠ r) : r ∉ (proxy G r a b).support := by
  rintro ⟨x,hx|hx⟩
  · exact hx.2.1 rfl
  · obtain ⟨i,hi⟩ := (pairGraph_adj a b r x).mp hx
    rcases (edge_adj _ _ _ _).mp hi with ⟨⟨h,_⟩|⟨h,_⟩,_⟩
    · exact ha i h.symm
    · exact hb i h.symm

lemma proxy_old_edges (G : SimpleGraph V) (r : V) (a b : I → V) (hab : ∀ i, a i ≠ b i)
    (hfresh : ∀ i, ¬G.Adj (a i) (b i)) :
    (proxy G r a b).edgeSet \ Set.range (fun i ↦ s(a i,b i))=(within G ({r}ᶜ : Set V)).edgeSet := by
  rw [proxy,edgeSet_sup,pairGraph_edges a b hab]
  ext e
  constructor
  · rintro ⟨he,hn⟩
    exact he.resolve_right hn
  · intro he
    refine ⟨Or.inl he,?_⟩
    rintro ⟨i,rfl⟩
    exact hfresh i he.1

lemma spokes_cover (G : SimpleGraph V) (r : V) (a b : I → V)
    (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i))
    (hN : ∀ x, G.Adj r x → ∃ i, x=a i ∨ x=b i) :
    G.edgeSet=(within G ({r}ᶜ : Set V)).edgeSet ∪ ⋃ i, ({s(r,a i),s(r,b i)} : Set (Sym2 V)) := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    constructor
    · intro hxy
      by_cases hx : x=r
      · subst x
        obtain ⟨i,hi|hi⟩ := hN y hxy
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl (by rw [hi])⟩)
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inr (Set.mem_singleton_iff.mpr (congrArg (fun y ↦ s(r,y)) hi))⟩)
      · by_cases hy : y=r
        · subst y
          obtain ⟨i,hi|hi⟩ := hN x hxy.symm
          · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl (by rw [hi]; exact Sym2.eq_swap)⟩)
          · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inr (by rw [hi]; exact Sym2.eq_swap)⟩)
        · exact Or.inl ⟨hxy,hx,hy⟩
    · rintro (hxy|hxy)
      · exact hxy.1
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hxy
        rcases hi with hi|hi
        · exact hi ▸ ha i
        · exact hi ▸ hb i

variable [Fintype V]

lemma restore_pairs (G : SimpleGraph V) (r : V) (a b : I → V)
    (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i)) (hab : ∀ i, a i ≠ b i)
    (hfresh : ∀ i, ¬G.Adj (a i) (b i))
    (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set V) {a j,b j}))
    (hN : ∀ x, G.Adj r x → ∃ i, x=a i ∨ x=b i)
    (D : Finset (proxy G r a b).Subgraph) (hD : GoodDecomposition (proxy G r a b) D)
    (hsep : Separated D (fun i ↦ s(a i,b i))) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  apply expand_through_center a b (proxy_pair_adj G r a b hab) r
    (proxy_avoids G r a b (fun i ↦ (ha i).ne.symm) (fun i ↦ (hb i).ne.symm)) ha hb hpairs _ D hD hsep
  rw [proxy_old_edges G r a b hab hfresh]
  exact spokes_cover G r a b ha hb hN

lemma restore_pairs_and_edge (G : SimpleGraph V) (r z : V) (hz : G.Adj r z) (a b : I → V)
    (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i)) (hab : ∀ i, a i ≠ b i)
    (haz : ∀ i, a i ≠ z) (hbz : ∀ i, b i ≠ z)
    (hfresh : ∀ i, ¬G.Adj (a i) (b i))
    (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set V) {a j,b j}))
    (hN : ∀ x, G.Adj r x → x=z ∨ ∃ i, x=a i ∨ x=b i)
    (D : Finset (proxy (G.deleteEdges {s(r,z)}) r a b).Subgraph)
    (hD : GoodDecomposition (proxy (G.deleteEdges {s(r,z)}) r a b) D)
    (hsep : Separated D (fun i ↦ s(a i,b i))) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  have hpair (x : V) (hx : x ≠ z) : s(r,x) ≠ s(r,z) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_,h⟩|⟨h,h'⟩
    · exact hx h
    · exact hx (h'.trans h)
  have ha' (i) : (G.deleteEdges {s(r,z)}).Adj r (a i) := deleteEdges_adj.mpr ⟨ha i,hpair _ (haz i)⟩
  have hb' (i) : (G.deleteEdges {s(r,z)}).Adj r (b i) := deleteEdges_adj.mpr ⟨hb i,hpair _ (hbz i)⟩
  have hN' (x) (hx : (G.deleteEdges {s(r,z)}).Adj r x) : ∃ i, x=a i ∨ x=b i := by
    have hh := deleteEdges_adj.mp hx
    apply (hN x hh.1).resolve_left
    intro he
    exact hh.2 (congrArg (fun x ↦ s(r,x)) he)
  obtain ⟨E,hE,hEc⟩ := restore_pairs (G.deleteEdges {s(r,z)}) r a b ha' hb' hab
    (fun i hi ↦ hfresh i hi.1) hpairs hN' D hD hsep
  obtain ⟨F,hF,hFc⟩ := restore_edge hz hE
  exact ⟨F,hF,hFc.trans (Nat.add_le_add_right hEc 1)⟩

lemma proxy_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (G : SimpleGraph (Fin n)) (r : Fin n) (a b : I → Fin n)
    (ha : ∀ i, a i ≠ r) (hb : ∀ i, b i ≠ r)
    (hc : SupportConnected (proxy G r a b)) :
    ∃ D : Finset (proxy G r a b).Subgraph, GoodDecomposition (proxy G r a b) D ∧
      D.card ≤ ⌈((n-1 : ℕ) : ℚ)/2⌉₊ := by
  have hr := proxy_avoids G r a b ha hb
  have hsub : (proxy G r a b).support ⊆ ({r}ᶜ : Set (Fin n)) := by
    intro x hx hxr
    exact hr ((Set.mem_singleton_iff.mp hxr) ▸ hx)
  have hbnd := Set.ncard_le_ncard hsub
  have hcS : ({r}ᶜ : Set (Fin n)).ncard=n-1 := by
    rw [Set.ncard_compl,Set.ncard_singleton,Nat.card_fin]
  rw [hcS] at hbnd
  have hn : 0 < n := Fin.pos r
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall (proxy G r a b) hc (by omega)
  refine ⟨D,hD,?_⟩
  rw [ceil_half] at hDc ⊢
  omega

lemma failure_proxy_collision {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (G : SimpleGraph (Fin n))
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (a b : I → Fin n)
    (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i)) (hab : ∀ i, a i ≠ b i)
    (hfresh : ∀ i, ¬G.Adj (a i) (b i))
    (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set (Fin n)) {a j,b j}))
    (hN : ∀ x, G.Adj r x → ∃ i, x=a i ∨ x=b i)
    (hc : SupportConnected (proxy G r a b)) :
    ∃ D : Finset (proxy G r a b).Subgraph, GoodDecomposition (proxy G r a b) D ∧
      D.card ≤ ⌈((n-1 : ℕ) : ℚ)/2⌉₊ ∧
      ∃ K ∈ D, ∃ i j, i ≠ j ∧ s(a i,b i) ∈ K.edgeSet ∧ s(a j,b j) ∈ K.edgeSet := by
  obtain ⟨D,hD,hDc⟩ := proxy_partition hsmall G r a b (fun i ↦ (ha i).ne.symm) (fun i ↦ (hb i).ne.symm) hc
  refine ⟨D,hD,hDc,?_⟩
  by_contra hno
  have hsep : Separated D (fun i ↦ s(a i,b i)) := by
    intro K hK i j hi hj
    by_contra hij
    exact hno ⟨K,hK,i,j,hij,hi,hj⟩
  obtain ⟨E,hE,hEc⟩ := restore_pairs G r a b ha hb hab hfresh hpairs hN D hD hsep
  apply hfail
  refine ⟨E,hE,?_⟩
  simp only [Fintype.card_fin,ceil_half] at hDc ⊢
  omega

lemma odd_failure_proxy_collision {n : ℕ} (hsmall : VertexCritical.SmallerOrders n) (hn : Odd n)
    (G : SimpleGraph (Fin n))
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r z : Fin n) (hz : G.Adj r z) (a b : I → Fin n)
    (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i)) (hab : ∀ i, a i ≠ b i)
    (haz : ∀ i, a i ≠ z) (hbz : ∀ i, b i ≠ z)
    (hfresh : ∀ i, ¬G.Adj (a i) (b i))
    (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set (Fin n)) {a j,b j}))
    (hN : ∀ x, G.Adj r x → x=z ∨ ∃ i, x=a i ∨ x=b i)
    (hc : SupportConnected (proxy (G.deleteEdges {s(r,z)}) r a b)) :
    ∃ D : Finset (proxy (G.deleteEdges {s(r,z)}) r a b).Subgraph,
      GoodDecomposition (proxy (G.deleteEdges {s(r,z)}) r a b) D ∧
      D.card ≤ ⌈((n-1 : ℕ) : ℚ)/2⌉₊ ∧
      ∃ K ∈ D, ∃ i j, i ≠ j ∧ s(a i,b i) ∈ K.edgeSet ∧ s(a j,b j) ∈ K.edgeSet := by
  obtain ⟨D,hD,hDc⟩ := proxy_partition hsmall (G.deleteEdges {s(r,z)}) r a b
    (fun i ↦ (ha i).ne.symm) (fun i ↦ (hb i).ne.symm) hc
  refine ⟨D,hD,hDc,?_⟩
  by_contra hno
  have hsep : Separated D (fun i ↦ s(a i,b i)) := by
    intro K hK i j hi hj
    by_contra hij
    exact hno ⟨K,hK,i,j,hij,hi,hj⟩
  obtain ⟨E,hE,hEc⟩ := restore_pairs_and_edge G r z hz a b ha hb hab haz hbz hfresh hpairs hN D hD hsep
  apply hfail
  refine ⟨E,hE,?_⟩
  simp only [Fintype.card_fin,ceil_half] at hDc ⊢
  obtain ⟨m,hm⟩ := hn
  omega

end Erdos583PairedSuppressionDevelopment
