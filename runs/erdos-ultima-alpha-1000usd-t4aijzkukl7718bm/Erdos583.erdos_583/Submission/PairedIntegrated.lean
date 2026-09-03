import Submission.SuppressionIntegrated

/-! Shared-center expansions, two-edge separation with one extra path, and conditional five-spoke reduction. -/
namespace Erdos583Work
/- Simultaneous fresh path expansions may share internal vertices if their
shortcut edges belong to different members of the original partition. -/
namespace SharedExpansion
open SimpleGraph _root_.Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
variable {V I : Type*} [Fintype V] {H G : SimpleGraph V}

def Separated (D : Finset H.Subgraph) (e : I → Sym2 V) : Prop :=
  ∀ K ∈ D, ∀ i j, e i ∈ K.edgeSet → e j ∈ K.edgeSet → i=j

lemma expand_separated_edges (a b : I → V) (hab : ∀ i, H.Adj (a i) (b i))
    (R : ∀ i, G.Walk (a i) (b i)) (hR : ∀ i, (R i).IsPath)
    (hfresh : ∀ i x, x ∈ (R i).support → x ≠ a i → x ≠ b i → x ∉ H.support)
    (hdis : Pairwise (fun i j ↦ Disjoint (R i).toSubgraph.edgeSet (R j).toSubgraph.edgeSet))
    (hcover : G.edgeSet=(H.edgeSet \ Set.range (fun i ↦ s(a i,b i))) ∪ ⋃ i, (R i).toSubgraph.edgeSet)
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (hsep : Separated D (fun i ↦ s(a i,b i))) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  let F := Set.range (fun i ↦ s(a i,b i))
  have hnewold (i : I) : Disjoint (R i).toSubgraph.edgeSet (H.edgeSet \ F) := by
    apply (expansion_path_disjoint_old_edges (R i) (hfresh i)).mono_right
    intro e he
    exact ⟨he.1,fun hh ↦ he.2 ⟨i,hh.symm⟩⟩
  have hex (K : D) : ∃ L : G.Subgraph, IsPathSubgraph L ∧
      L.edgeSet=(K.val.edgeSet \ F) ∪ ⋃ i, (if s(a i,b i) ∈ K.val.edgeSet then (R i).toSubgraph.edgeSet else ∅) := by
    obtain ⟨u,v,p,hp,hK⟩ := hD.1 K.val K.property
    by_cases ht : ∃ i, s(a i,b i) ∈ K.val.edgeSet
    · obtain ⟨i,hi⟩ := ht
      have honly (j) (hj : s(a j,b j) ∈ K.val.edgeSet) : j=i := hsep K.val K.property j i hj hi
      have htransfer : ∀ e ∈ p.edges, e ∈ K.val.spanningCoe.edgeSet := by
        intro e he
        change e ∈ K.val.edgeSet
        rw [hK]
        exact p.mem_edges_toSubgraph.mpr he
      let q := p.transfer K.val.spanningCoe htransfer
      have hq : q.IsPath := hp.transfer htransfer
      have hqe : q.toSubgraph.edgeSet=K.val.edgeSet := by
        ext e
        simp only [q,Walk.mem_edges_toSubgraph,Walk.edges_transfer,hK]
      have hrest : K.val.spanningCoe.deleteEdges {s(a i,b i)} ≤ G := by
        intro x y hxy
        have hh : s(x,y) ∈ K.val.edgeSet ∧ s(x,y) ≠ s(a i,b i) := by
          simpa only [deleteEdges_adj,Set.mem_singleton_iff] using hxy
        have ho : s(x,y) ∉ F := by
          rintro ⟨j,hj⟩
          dsimp only at hj
          have hjK : s(a j,b j) ∈ K.val.edgeSet := by rw [hj]; exact hh.1
          exact hh.2 (hj.symm.trans (congrArg (fun j ↦ s(a j,b j)) (honly j hjK)))
        change s(x,y) ∈ G.edgeSet
        rw [hcover]
        exact Or.inl ⟨K.val.edgeSet_subset hh.1,ho⟩
      have hfr : ∀ x ∈ (R i).support, x ≠ a i → x ≠ b i → x ∉ K.val.spanningCoe.support := by
        intro x hx hxa hxb hxs
        exact hfresh i x hx hxa hxb (by
          obtain ⟨y,hy⟩ := hxs
          exact ⟨y,K.val.adj_sub hy⟩)
      obtain ⟨P,hP,hPe⟩ := path_expand_edge (R i) (hR i) hrest hfr q hq
      have hie : s(a i,b i) ∈ q.edges := by rw [←Walk.mem_edges_toSubgraph,hqe]; exact hi
      refine ⟨P.toSubgraph,⟨u,v,P,hP,rfl⟩,?_⟩
      rw [hPe,if_pos hie,hqe]
      have hdiff : K.val.edgeSet \ {s(a i,b i)}=K.val.edgeSet \ F := by
        ext e
        constructor
        · rintro ⟨he,hne⟩
          refine ⟨he,?_⟩
          rintro ⟨j,hj⟩
          dsimp only at hj
          have hjK : s(a j,b j) ∈ K.val.edgeSet := by rw [hj]; exact he
          have hji := honly j hjK
          exact hne (Set.mem_singleton_iff.mpr (hj.symm.trans (congrArg (fun j ↦ s(a j,b j)) hji)))
        · rintro ⟨he,hne⟩
          exact ⟨he,fun hh ↦ hne ⟨i,(Set.mem_singleton_iff.mp hh).symm⟩⟩
      rw [hdiff]
      congr 1
      ext e
      constructor
      · intro he
        exact Set.mem_iUnion.mpr ⟨i,by simpa only [if_pos hi] using he⟩
      · intro he
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
        split_ifs at hj with hjK
        · exact (honly j hjK) ▸ hj
        · exact hj.elim
    · have hno (i) : s(a i,b i) ∉ K.val.edgeSet := fun hi ↦ ht ⟨i,hi⟩
      have htransfer : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
        intro e he
        have heK : e ∈ K.val.edgeSet := by rw [hK]; exact p.mem_edges_toSubgraph.mpr he
        rw [hcover]
        exact Or.inl ⟨K.val.edgeSet_subset heK,by rintro ⟨i,rfl⟩; exact hno i heK⟩
      let P := p.transfer G htransfer
      refine ⟨P.toSubgraph,⟨u,v,P,hp.transfer htransfer,rfl⟩,?_⟩
      simp only [if_neg (hno _),Set.iUnion_empty,Set.union_empty]
      ext e
      simp only [P,Walk.mem_edges_toSubgraph,Walk.edges_transfer,Set.mem_diff]
      constructor
      · intro he
        have heK : e ∈ K.val.edgeSet := by rw [hK]; exact p.mem_edges_toSubgraph.mpr he
        exact ⟨heK,by rintro ⟨i,rfl⟩; exact hno i heK⟩
      · intro he
        rw [hK] at he
        exact p.mem_edges_toSubgraph.mp he.1
  choose f hpath heq using hex
  have hmem (K : D) (e : Sym2 V) : e ∈ (f K).edgeSet ↔
      (e ∈ K.val.edgeSet ∧ e ∉ F) ∨ ∃ i, s(a i,b i) ∈ K.val.edgeSet ∧ e ∈ (R i).toSubgraph.edgeSet := by
    rw [heq]
    simp only [Set.mem_union,Set.mem_diff,Set.mem_iUnion]
    apply or_congr Iff.rfl
    apply exists_congr
    intro i
    by_cases hi : s(a i,b i) ∈ K.val.edgeSet <;> simp only [hi,if_true,if_false,Set.mem_empty_iff_false,true_and,false_and]
  have hpair : Pairwise (fun K L : D ↦ Disjoint (f K).edgeSet (f L).edgeSet) := by
    intro K L hKL
    have hd := hD.2.1 K.property L.property (fun h ↦ hKL (Subtype.ext h))
    apply Set.disjoint_left.mpr
    intro e heK heL
    rcases (hmem K e).mp heK with ⟨heK,heF⟩|⟨i,hi,hei⟩ <;>
      rcases (hmem L e).mp heL with ⟨heL,heF'⟩|⟨j,hj,hej⟩
    · exact Set.disjoint_left.mp hd heK heL
    · exact Set.disjoint_left.mp (hnewold j) hej ⟨K.val.edgeSet_subset heK,heF⟩
    · exact Set.disjoint_left.mp (hnewold i) hei ⟨L.val.edgeSet_subset heL,heF'⟩
    · by_cases hij : i=j
      · subst j
        exact Set.disjoint_left.mp hd hi hj
      · exact Set.disjoint_left.mp (hdis hij) hei hej
  have hcov : (⋃ K : D, (f K).edgeSet)=G.edgeSet := by
    ext e
    constructor
    · rintro he
      obtain ⟨K,hK⟩ := Set.mem_iUnion.mp he
      exact (f K).edgeSet_subset hK
    · intro he
      rw [hcover] at he
      rcases he with ⟨he,heF⟩|he
      · have heD := hD.2.2.symm ▸ he
        obtain ⟨K,heK⟩ := Set.mem_iUnion.mp heD
        obtain ⟨hK,heK⟩ := Set.mem_iUnion.mp heK
        exact Set.mem_iUnion.mpr ⟨⟨K,hK⟩,(hmem ⟨K,hK⟩ e).mpr (Or.inl ⟨heK,heF⟩)⟩
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
        have heD : s(a i,b i) ∈ ⋃ K ∈ D, K.edgeSet := hD.2.2.symm ▸ hab i
        obtain ⟨K,heK⟩ := Set.mem_iUnion.mp heD
        obtain ⟨hK,heK⟩ := Set.mem_iUnion.mp heK
        exact Set.mem_iUnion.mpr ⟨⟨K,hK⟩,(hmem ⟨K,hK⟩ e).mpr (Or.inr ⟨i,heK,hi⟩)⟩
  obtain ⟨E,hE,hEc⟩ := MatchingCutGlue.indexed_decomposition f hpath hpair hcov
  exact ⟨E,hE,by simpa only [Fintype.card_coe] using hEc⟩

lemma expand_through_center (a b : I → V) (hab : ∀ i, H.Adj (a i) (b i))
    (r : V) (hr : r ∉ H.support)
    (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i))
    (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set V) {a j,b j}))
    (hcover : G.edgeSet=(H.edgeSet \ Set.range (fun i ↦ s(a i,b i))) ∪
      ⋃ i, ({s(r,a i),s(r,b i)} : Set (Sym2 V)))
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (hsep : Separated D (fun i ↦ s(a i,b i))) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  let R (i) : G.Walk (a i) (b i) := .cons (ha i).symm (.cons (hb i) .nil)
  have hR (i) : (R i).IsPath := by
    simp [R,Walk.cons_isPath_iff,(ha i).ne.symm,(hb i).ne,(hab i).ne]
  have he (i) : (R i).toSubgraph.edgeSet=({s(r,a i),s(r,b i)} : Set (Sym2 V)) := by
    ext e
    simp [R,Sym2.eq_swap,or_comm]
  have hfr (i) (x) (hx : x ∈ (R i).support) (hxa : x ≠ a i) (hxb : x ≠ b i) : x ∉ H.support := by
    have hxr : x=r := by simpa [R,Walk.support,hxa,hxb] using hx
    exact hxr ▸ hr
  have hpair (x y : V) : s(r,x)=s(r,y) → x=y := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_,hxy⟩|⟨hry,hxr⟩
    · exact hxy
    · exact hxr.trans hry
  have hd : Pairwise (fun i j ↦ Disjoint (R i).toSubgraph.edgeSet (R j).toSubgraph.edgeSet) := by
    intro i j hij
    rw [he,he]
    apply Set.disjoint_left.mpr
    intro e hei hej
    rcases hei with hei|hei <;> rcases hej with hej|hej
    · exact Set.disjoint_left.mp (hpairs hij) (Or.inl rfl) (Or.inl (hpair _ _ (hei.symm.trans hej)))
    · exact Set.disjoint_left.mp (hpairs hij) (Or.inl rfl) (Or.inr (hpair _ _ (hei.symm.trans hej)))
    · exact Set.disjoint_left.mp (hpairs hij) (Or.inr rfl) (Or.inl (hpair _ _ (hei.symm.trans hej)))
    · exact Set.disjoint_left.mp (hpairs hij) (Or.inr rfl) (Or.inr (hpair _ _ (hei.symm.trans hej)))
  exact expand_separated_edges a b hab R hR hfr hd (by simpa only [he] using hcover) D hD hsep

lemma expand_through_center_and_edge (a b : I → V) (hab : ∀ i, H.Adj (a i) (b i))
    (r z : V) (hr : r ∉ H.support) (hz : G.Adj r z)
    (ha : ∀ i, G.Adj r (a i)) (hb : ∀ i, G.Adj r (b i))
    (haz : ∀ i, a i ≠ z) (hbz : ∀ i, b i ≠ z)
    (hpairs : Pairwise (fun i j ↦ Disjoint ({a i,b i} : Set V) {a j,b j}))
    (hcover : (G.deleteEdges {s(r,z)}).edgeSet=(H.edgeSet \ Set.range (fun i ↦ s(a i,b i))) ∪
      ⋃ i, ({s(r,a i),s(r,b i)} : Set (Sym2 V)))
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (hsep : Separated D (fun i ↦ s(a i,b i))) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  have hpair (x : V) (hx : x ≠ z) : s(r,x) ≠ s(r,z) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_,h⟩|⟨h,h'⟩
    · exact hx h
    · exact hx (h'.trans h)
  have ha' (i) : (G.deleteEdges {s(r,z)}).Adj r (a i) :=
    deleteEdges_adj.mpr ⟨ha i,hpair _ (haz i)⟩
  have hb' (i) : (G.deleteEdges {s(r,z)}).Adj r (b i) :=
    deleteEdges_adj.mpr ⟨hb i,hpair _ (hbz i)⟩
  obtain ⟨E,hE,hEc⟩ := expand_through_center a b hab r hr ha' hb' hpairs hcover D hD hsep
  obtain ⟨F,hF,hFc⟩ := restore_edge hz hE
  exact ⟨F,hF,hFc.trans (Nat.add_le_add_right hEc 1)⟩

end SharedExpansion

/- Pairing the spokes at a vertex gives a valid reduction when the shortcut
edges are separated by the inductive path partition. No existence theorem for
such a separated partition is assumed here. -/
namespace PairedSuppression
open SimpleGraph _root_.Erdos583Work _root_.Erdos583Work.BridgeGlue
open _root_.Erdos583Work.SharedExpansion
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

end PairedSuppression

/- Two distinct edges can always be separated by splitting one path, with
at most one additional member. This is not a same-budget separation theorem. -/
namespace SeparateTwoEdges
open SimpleGraph _root_.Erdos583Work _root_.Erdos583Work.RootedTailSystem
open _root_.Erdos583Work.SharedExpansion
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V}

lemma two_separated_iff (D : Finset G.Subgraph) (e f : Sym2 V) :
    Separated D ![e,f] ↔ ∀ K ∈ D, ¬(e ∈ K.edgeSet ∧ f ∈ K.edgeSet) := by
  constructor
  · intro h K hK ⟨he,hf⟩
    have hh := h K hK 0 1 he hf
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  · intro h K hK i j hi hj
    fin_cases i <;> fin_cases j
    · rfl
    · exact (h K hK ⟨hi,hj⟩).elim
    · exact (h K hK ⟨hj,hi⟩).elim
    · rfl

lemma split_path_two_edges {u v : V} (P : G.Walk u v) (hP : P.IsPath)
    (e f : Sym2 V) (hef : e ≠ f) (he : e ∈ P.edges) (hf : f ∈ P.edges) :
    ∃ L M : G.Subgraph, IsPathSubgraph L ∧ IsPathSubgraph M ∧
      Disjoint L.edgeSet M.edgeSet ∧ L.edgeSet ∪ M.edgeSet=P.toSubgraph.edgeSet ∧
      e ∈ L.edgeSet ∧ f ∈ M.edgeSet := by
  classical
  obtain ⟨a,b,hab,q,r,rfl,rfl⟩ := walk_split_at_edge P e he
  have hf' : f ∈ q.edges ∨ f ∈ r.edges := by
    simpa only [Walk.edges_append,Walk.edges_cons,List.mem_append,List.mem_cons,hef.symm,false_or] using hf
  rcases hf' with hfq|hfr
  · have hd := append_trail_disjoint hP.isTrail
    refine ⟨(Walk.cons hab r).toSubgraph,q.toSubgraph,
      ⟨_,_,_,hP.of_append_right,rfl⟩,⟨_,_,_,hP.of_append_left,rfl⟩,hd.symm,?_,?_,?_⟩
    · rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup,Set.union_comm]
    · rw [Walk.mem_edges_toSubgraph]; exact List.mem_cons_self
    · exact q.mem_edges_toSubgraph.mpr hfq
  · have hform : (q.concat hab).append r=q.append (Walk.cons hab r) := Walk.concat_append q hab r
    have hp : ((q.concat hab).append r).IsPath := hform.symm ▸ hP
    refine ⟨(q.concat hab).toSubgraph,r.toSubgraph,
      ⟨_,_,_,hp.of_append_left,rfl⟩,⟨_,_,_,hp.of_append_right,rfl⟩,append_trail_disjoint hp.isTrail,?_,?_,?_⟩
    · rw [←Subgraph.edgeSet_sup,←Walk.toSubgraph_append,hform]
    · simp only [Walk.mem_edges_toSubgraph,Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton,or_true]
    · exact r.mem_edges_toSubgraph.mpr hfr

lemma split_member_two_edges (D : Finset G.Subgraph) (hD : GoodDecomposition G D)
    (K : G.Subgraph) (hK : K ∈ D) (e f : Sym2 V) (hef : e ≠ f)
    (he : e ∈ K.edgeSet) (hf : f ∈ K.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 ∧ Separated E ![e,f] := by
  classical
  obtain ⟨u,v,P,hP,hKP⟩ := hD.1 K hK
  have heP : e ∈ P.edges := P.mem_edges_toSubgraph.mp (hKP ▸ he)
  have hfP : f ∈ P.edges := P.mem_edges_toSubgraph.mp (hKP ▸ hf)
  obtain ⟨L,M,hL,hM,hLM,hcov,heL,hfM⟩ := split_path_two_edges P hP e f hef heP hfP
  rw [←hKP] at hcov
  have hLK : L.edgeSet ⊆ K.edgeSet := hcov ▸ Set.subset_union_left
  have hMK : M.edgeSet ⊆ K.edgeSet := hcov ▸ Set.subset_union_right
  have hLD (J) (hJ : J ∈ D.erase K) : Disjoint L.edgeSet J.edgeSet :=
    (hD.2.1 hK (Finset.mem_of_mem_erase hJ) (Finset.mem_erase.mp hJ).1.symm).mono_left hLK
  have hMD (J) (hJ : J ∈ D.erase K) : Disjoint M.edgeSet J.edgeSet :=
    (hD.2.1 hK (Finset.mem_of_mem_erase hJ) (Finset.mem_erase.mp hJ).1.symm).mono_left hMK
  let E := insert L (insert M (D.erase K))
  have hgood : GoodDecomposition G E := by
    refine ⟨?_,?_,?_⟩
    · intro J hJ
      rcases Finset.mem_insert.mp hJ with hJ|hJ
      · exact hJ ▸ hL
      rcases Finset.mem_insert.mp hJ with hJ|hJ
      · exact hJ ▸ hM
      · exact hD.1 J (Finset.mem_of_mem_erase hJ)
    · dsimp only [E]
      rw [Finset.coe_insert,Set.pairwiseDisjoint_insert]
      constructor
      · rw [Finset.coe_insert,Set.pairwiseDisjoint_insert]
        constructor
        · intro J hJ Q hQ hJQ
          exact hD.2.1 (Finset.mem_of_mem_erase hJ) (Finset.mem_of_mem_erase hQ) hJQ
        · intro J hJ _; exact hMD J hJ
      · intro J hJ _
        rcases Finset.mem_insert.mp hJ with hJ|hJ
        · exact hJ ▸ hLM
        · exact hLD J hJ
    · ext z
      constructor
      · intro hz
        obtain ⟨J,hz⟩ := Set.mem_iUnion.mp hz
        obtain ⟨_,hz⟩ := Set.mem_iUnion.mp hz
        exact J.edgeSet_subset hz
      · intro hz
        have hzD := hD.2.2.symm ▸ hz
        obtain ⟨J,hzJ⟩ := Set.mem_iUnion.mp hzD
        obtain ⟨hJD,hzJ⟩ := Set.mem_iUnion.mp hzJ
        by_cases hJK : J=K
        · subst J
          rw [←hcov] at hzJ
          rcases hzJ with hzL|hzM
          · exact Set.mem_iUnion.mpr ⟨L,Set.mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,hzL⟩⟩
          · exact Set.mem_iUnion.mpr ⟨M,Set.mem_iUnion.mpr
              ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),hzM⟩⟩
        · exact Set.mem_iUnion.mpr ⟨J,Set.mem_iUnion.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hJK,hJD⟩)),hzJ⟩⟩
  refine ⟨E,hgood,?_,?_⟩
  · have h1 := Finset.card_insert_le L (insert M (D.erase K))
    have h2 := Finset.card_insert_le M (D.erase K)
    have h3 := Finset.card_erase_add_one hK
    dsimp only [E]
    omega
  · apply (two_separated_iff E e f).mpr
    intro J hJ ⟨heJ,hfJ⟩
    rcases Finset.mem_insert.mp hJ with hJ|hJ
    · subst J
      exact Set.disjoint_left.mp hLM hfJ hfM
    rcases Finset.mem_insert.mp hJ with hJ|hJ
    · subst J
      exact Set.disjoint_left.mp hLM heL heJ
    · exact Set.disjoint_left.mp
        (hD.2.1 hK (Finset.mem_of_mem_erase hJ) (Finset.mem_erase.mp hJ).1.symm) he heJ

lemma separate_two_edges (D : Finset G.Subgraph) (hD : GoodDecomposition G D)
    (e f : Sym2 V) (hef : e ≠ f) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 ∧ Separated E ![e,f] := by
  classical
  by_cases hs : Separated D ![e,f]
  · exact ⟨D,hD,Nat.le_succ _,hs⟩
  · have hh : ∃ K ∈ D, e ∈ K.edgeSet ∧ f ∈ K.edgeSet := by
      by_contra hn
      exact hs ((two_separated_iff D e f).mpr (fun K hK h ↦ hn ⟨K,hK,h⟩))
    obtain ⟨K,hK,he,hf⟩ := hh
    exact split_member_two_edges D hD K hK e f hef he hf

end SeparateTwoEdges

/- A five-spoke reduction with an explicit two-shortcut collision alternative.
A smallest odd-order failure forces a saturated proxy and forces the two
shortcut edges into the same member of every budget-sized proxy partition. -/
namespace FiveSpokeReduction
open SimpleGraph _root_.Erdos583Work _root_.Erdos583Work.BridgeGlue
open _root_.Erdos583Work.SharedExpansion _root_.Erdos583Work.PairedSuppression
open _root_.Erdos583Work.SeparateTwoEdges
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
end FiveSpokeReduction

end Erdos583Work
