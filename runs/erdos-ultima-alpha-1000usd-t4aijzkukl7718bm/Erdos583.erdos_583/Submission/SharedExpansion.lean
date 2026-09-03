import Submission.SuppressionIntegrated

/-! Simultaneous fresh path expansions may share internal vertices if their
shortcut edges belong to different members of the original partition. -/
namespace Erdos583SharedExpansionDevelopment
open SimpleGraph Erdos583Work
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

end Erdos583SharedExpansionDevelopment
