import Submission.Work

/-! Compression of a two-terminal path region; no global marking hypothesis. -/
namespace Erdos583CorridorReductionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*} {G : SimpleGraph V}

noncomputable def proxy (G : SimpleGraph V) (S : Set V) (u a v : V) : SimpleGraph V :=
  (within G Sᶜ ⊔ edge u a) ⊔ edge a v

lemma proxy_support_subset (S : Set V) {u a v : V} (hu : u ∉ S) (hv : v ∉ S) :
    (proxy G S u a v).support ⊆ insert a Sᶜ := by
  intro x hx
  obtain ⟨y,hy⟩ := (mem_support _).mp hx
  rcases hy with (hy|hy)|hy
  · exact Or.inr hy.2.1
  · rcases (edge_adj u a x y).mp hy with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
    · exact Or.inr hu
    · exact Or.inl rfl
  · rcases (edge_adj a v x y).mp hy with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
    · exact Or.inl rfl
    · exact Or.inr hv

lemma proxy_delete_edge (S : Set V) {u a v : V}
    (ha : a ∈ S) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v) :
    (proxy G S u a v).edgeSet \ {s(a,v)} = (within G Sᶜ).edgeSet ∪ {s(u,a)} := by
  have hau : a ≠ u := fun h ↦ hu (h ▸ ha)
  have hav : a ≠ v := fun h ↦ hv (h ▸ ha)
  have hn : ¬(within G Sᶜ ⊔ edge u a).Adj a v := by
    rintro (hh|hh)
    · exact hh.2.1 ha
    · simp only [edge_adj] at hh
      rcases hh.1 with ⟨h,_⟩|⟨_,h⟩
      · exact hau h
      · exact huv h.symm
  rw [proxy,edgeSet_sup_edge_diff _ hav hn,edgeSet_sup,edge_edgeSet_of_ne hau.symm]

lemma proxy_connected (S : Set V) {u a v : V}
    (hG : G.Connected) (ha : a ∈ S) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (R : G.Walk a v) (hR : ∀ x ∈ R.support, x ∈ S ∨ x=v)
    (K : G.Subgraph) (hK : K.verts ⊆ S)
    (hc : G.edgeSet = ((within G Sᶜ).edgeSet ∪ {s(u,a)}) ∪ R.toSubgraph.edgeSet ∪ K.edgeSet) :
    SupportConnected (proxy G S u a v) := by
  classical
  let H := proxy G S u a v
  let f : V → V := fun x ↦ if x ∈ S then a else x
  have hau : a ≠ u := fun h ↦ hu (h ▸ ha)
  have hav : a ≠ v := fun h ↦ hv (h ▸ ha)
  have hua : H.Adj u a := Or.inl (Or.inr ((edge_adj u a u a).mpr ⟨Or.inl ⟨rfl,rfl⟩,hau.symm⟩))
  have havH : H.Adj a v := Or.inr ((edge_adj a v a v).mpr ⟨Or.inl ⟨rfl,rfl⟩,hav⟩)
  have hf (x y : V) (hxy : G.Adj x y) : H.Reachable (f x) (f y) := by
    have he : s(x,y) ∈ G.edgeSet := hxy
    rw [hc] at he
    rcases he with ((he|he)|he)|he
    · simpa only [f,if_neg he.2.1,if_neg he.2.2] using
        (show H.Adj x y from Or.inl (Or.inl he)).reachable
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simpa only [f,if_neg hu,if_pos ha] using hua.reachable
      · simpa only [f,if_neg hu,if_pos ha] using hua.reachable.symm
    · have hx := hR x (Walk.mem_support_of_adj_toSubgraph he)
      have hy := hR y (Walk.mem_support_of_adj_toSubgraph (R.toSubgraph.symm he))
      rcases hx with hx|rfl <;> rcases hy with hy|rfl
      · simp only [f,if_pos hx,if_pos hy]; exact .rfl
      · simpa only [f,if_pos hx,if_neg hv] using havH.reachable
      · simpa only [f,if_pos hy,if_neg hv] using havH.reachable.symm
      · exact .rfl
    · have hx := hK (K.edge_vert he)
      have hy := hK (K.edge_vert (K.symm he))
      simp only [f,if_pos hx,if_pos hy]
      exact .rfl
  have hfix (x : V) (hx : x ∈ H.support) : f x=x := by
    rcases proxy_support_subset S hu hv hx with rfl|hx
    · simp only [f,if_pos ha]
    · simp only [f,if_neg hx]
  intro x hx y hy
  simpa only [hfix x hx,hfix y hy] using reachable_map_to_reachable f hf (hG.preconnected x y)

lemma restore_partitioned_subgraph (K : G.Subgraph) (A : Finset G.Subgraph)
    (hA : ∀ J ∈ A, IsPathSubgraph J)
    (hdA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun J ↦ J.edgeSet))
    (hcA : (⋃ J ∈ A, J.edgeSet)=K.edgeSet)
    {D : Finset (G.deleteEdges K.edgeSet).Subgraph}
    (hD : GoodDecomposition (G.deleteEdges K.edgeSet) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+A.card := by
  classical
  let F := G.deleteEdges K.edgeSet
  let hFG : F ≤ G := G.deleteEdges_le _
  let D' := D.image (Subgraph.map (Hom.ofLE hFG))
  have hpaths : ∀ J ∈ D', IsPathSubgraph J := by
    intro J hJ
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hJ
    exact lift_path_subgraph hFG (hD.1 L hL)
  have hd := hD.2.lift_pairwise hFG
  have hcover := hD.2.lift_union hFG
  change (⋃ J ∈ D', J.edgeSet)=F.edgeSet at hcover
  obtain ⟨E,hE,hEc⟩ := CutVertexReduction.union_disjoint_partitions D' A hpaths hA hd hdA
    (by
      intro J hJ L hL
      apply Set.disjoint_left.mpr
      intro e heJ heL
      have heF : e ∈ F.edgeSet := hcover ▸ Set.mem_iUnion.mpr ⟨J,Set.mem_iUnion.mpr ⟨hJ,heJ⟩⟩
      have heK : e ∈ K.edgeSet := hcA ▸ Set.mem_iUnion.mpr ⟨L,Set.mem_iUnion.mpr ⟨hL,heL⟩⟩
      rw [show F=G.deleteEdges K.edgeSet from rfl,edgeSet_deleteEdges] at heF
      exact heF.2 heK)
    (by
      rw [hcover,hcA,show F=G.deleteEdges K.edgeSet from rfl,edgeSet_deleteEdges]
      exact Set.diff_union_of_subset K.edgeSet_subset)
  exact ⟨E,hE,hEc.trans (Nat.add_le_add_right Finset.card_image_le _)⟩

lemma restore_proxy_corridor [Fintype V] (S : Set V) {u a v : V}
    (ha : a ∈ S) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (R : G.Walk a v) (hpR : R.IsPath) (hR : ∀ x ∈ R.support, x ∈ S ∨ x=v)
    (K : G.Subgraph) (hK : K.verts ⊆ S)
    (hd : Disjoint R.toSubgraph.edgeSet K.edgeSet)
    (hc : G.edgeSet = ((within G Sᶜ).edgeSet ∪ {s(u,a)}) ∪ R.toSubgraph.edgeSet ∪ K.edgeSet)
    (A : Finset G.Subgraph) (hA : ∀ J ∈ A, IsPathSubgraph J)
    (hdA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun J ↦ J.edgeSet))
    (hcA : (⋃ J ∈ A, J.edgeSet)=K.edgeSet)
    {D : Finset (proxy G S u a v).Subgraph} (hD : GoodDecomposition (proxy G S u a v) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+A.card := by
  classical
  let F := G.deleteEdges K.edgeSet
  have hRF (e : Sym2 V) (he : e ∈ R.edges) : e ∈ F.edgeSet := by
    rw [show F=G.deleteEdges K.edgeSet from rfl,edgeSet_deleteEdges]
    exact ⟨R.edges_subset_edgeSet he,fun hk ↦ Set.disjoint_left.mp hd (R.mem_edges_toSubgraph.mpr he) hk⟩
  let Q := R.transfer F hRF
  have hQ : Q.IsPath := hpR.transfer hRF
  have hQe : Q.toSubgraph.edgeSet=R.toSubgraph.edgeSet := by simp [Q,Walk.edgeSet_toSubgraph]
  have hfresh : ∀ x ∈ Q.support, x ≠ a → x ≠ v → x ∉ (proxy G S u a v).support := by
    intro x hx hxa hxv hxH
    have hxS : x ∈ S := (hR x (by simpa only [Q,Walk.support_transfer] using hx)).resolve_right hxv
    rcases proxy_support_subset S hu hv hxH with hxa'|hxout
    · exact hxa hxa'
    · exact hxout hxS
  have hbase : Disjoint ((within G Sᶜ).edgeSet ∪ {s(u,a)}) K.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hk
    rcases he with he|he
    · induction e using Sym2.ind with
      | h x y => exact he.2.1 (hK (K.edge_vert hk))
    · subst e
      exact hu (hK (K.edge_vert hk))
  have hcover : F.edgeSet = ((proxy G S u a v).edgeSet \ {s(a,v)}) ∪ Q.toSubgraph.edgeSet := by
    rw [proxy_delete_edge S ha hu hv huv,hQe]
    rw [show F=G.deleteEdges K.edgeSet from rfl,edgeSet_deleteEdges]
    rw [hc]
    ext e
    constructor
    · rintro ⟨he,hn⟩
      exact he.resolve_right hn
    · intro he
      refine ⟨Or.inl he,?_⟩
      intro hk
      exact he.elim (fun hh ↦ Set.disjoint_left.mp hbase hh hk) (fun hh ↦ Set.disjoint_left.mp hd hh hk)
  have hav : a ≠ v := fun h ↦ hv (h ▸ ha)
  obtain ⟨D',hD',hDc⟩ := hD.expand_edge
    (show (proxy G S u a v).Adj a v from Or.inr ((edge_adj a v a v).mpr ⟨Or.inl ⟨rfl,rfl⟩,hav⟩))
    Q hQ hfresh hcover
  obtain ⟨E,hE,hEc⟩ := restore_partitioned_subgraph K A hA hdA hcA hD'
  exact ⟨E,hE,by omega⟩

lemma corridor_budget {n q : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)}
    (hG : G.Connected) (S : Set (Fin n)) {u a v : Fin n}
    (ha : a ∈ S) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (R : G.Walk a v) (hpR : R.IsPath) (hR : ∀ x ∈ R.support, x ∈ S ∨ x=v)
    (K : G.Subgraph) (hK : K.verts ⊆ S)
    (hd : Disjoint R.toSubgraph.edgeSet K.edgeSet)
    (hc : G.edgeSet = ((within G Sᶜ).edgeSet ∪ {s(u,a)}) ∪ R.toSubgraph.edgeSet ∪ K.edgeSet)
    (A : Finset G.Subgraph) (hA : ∀ J ∈ A, IsPathSubgraph J)
    (hdA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun J ↦ J.edgeSet))
    (hcA : (⋃ J ∈ A, J.edgeSet)=K.edgeSet) (hAc : A.card ≤ q)
    (hq : 0 < q) (hsize : 2*q+1 ≤ S.ncard) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  have hconn := proxy_connected S hG ha hu hv huv R hR K hK hc
  have hs := Set.ncard_mono (proxy_support_subset (G := G) (a := a) S hu hv)
  have hsum : S.ncard+Sᶜ.ncard=n := by simpa using S.ncard_add_ncard_compl
  have hcount : (proxy G S u a v).support.ncard+2*q ≤ n := by
    have hi := Set.ncard_insert_le a Sᶜ
    omega
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall
    (proxy G S u a v) hconn (by omega)
  obtain ⟨E,hE,hEc⟩ := restore_proxy_corridor S ha hu hv huv R hpR hR K hK hd hc A hA hdA hcA hD
  refine ⟨E,hE,?_⟩
  rw [ceil_half] at hDc
  simp only [Fintype.card_fin,ceil_half]
  omega

lemma cycle_two_path_cover [Fintype V] {r : V} (C : G.Walk r r) (hC : C.IsCycle) :
    TriangleAbsorption.TwoPathCover (G := G) C.toSubgraph.edgeSet := by
  have hcard : C.toSubgraph.verts.ncard=C.length := by
    rw [Walk.verts_toSubgraph]
    exact cycle_support_ncard hC
  have hnp : ¬C.IsPath := by
    intro hp
    have hh := (QuotaSurgery.walk_vertex_ncard_eq_iff C).mpr hp
    omega
  exact MemberNormalExpansion.one_defect_two_paths C hC.isTrail hnp hcard

lemma cycle_corridor_budget {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)}
    (hG : G.Connected) {r u a v : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hlen : 5 ≤ C.length) (ha : a ∈ C.support) (hu : u ∉ C.support) (hv : v ∉ C.support)
    (huv : u ≠ v) (R : G.Walk a v) (hpR : R.IsPath)
    (hR : ∀ x ∈ R.support, x ∈ C.support ∨ x=v)
    (hd : Disjoint R.toSubgraph.edgeSet C.toSubgraph.edgeSet)
    (hc : G.edgeSet = ((within G {x | x ∉ C.support}).edgeSet ∪ {s(u,a)}) ∪
      R.toSubgraph.edgeSet ∪ C.toSubgraph.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  obtain ⟨A,hA,hdA,hAc,hAs⟩ := MemberNormalExpansion.two_path_parts (cycle_two_path_cover C hC)
  exact corridor_budget (q := 2) hsmall hG {x | x ∈ C.support} ha hu hv huv R hpR hR
    C.toSubgraph (fun x hx ↦ C.mem_verts_toSubgraph.mp hx) hd hc A hA hdA hAc hAs (by decide)
    (by simpa only [cycle_support_ncard hC] using hlen)

lemma two_terminal_cycle_cover {r u a b v : V} (C : G.Walk r r) (P : G.Walk a b)
    (hua : G.Adj u a) (hbv : G.Adj b v)
    (hu : u ∉ C.support) (hv : v ∉ C.support)
    (hinside : (within G {x | x ∈ C.support}).edgeSet=P.toSubgraph.edgeSet ∪ C.toSubgraph.edgeSet)
    (hcross : ∀ x ∈ C.support, ∀ y ∉ C.support, G.Adj x y → (x=a ∧ y=u) ∨ (x=b ∧ y=v)) :
    G.edgeSet = ((within G {x | x ∉ C.support}).edgeSet ∪ {s(u,a)}) ∪
      (P.concat hbv).toSubgraph.edgeSet ∪ C.toSubgraph.edgeSet := by
  have hPe : (P.concat hbv).toSubgraph.edgeSet=P.toSubgraph.edgeSet ∪ {s(b,v)} := by
    ext e
    simp only [Walk.edgeSet_toSubgraph,Set.mem_setOf_eq,Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton,
      Set.mem_union,Set.mem_singleton_iff]
  rw [hPe]
  ext e
  induction e using Sym2.ind with
  | h x y =>
    constructor
    · intro hxy
      by_cases hx : x ∈ C.support <;> by_cases hy : y ∈ C.support
      · have hh : s(x,y) ∈ (within G {x | x ∈ C.support}).edgeSet := ⟨hxy,hx,hy⟩
        rw [hinside] at hh
        exact hh.elim (fun hh ↦ Or.inl (Or.inr (Or.inl hh))) Or.inr
      · rcases hcross x hx y hy hxy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact Or.inl (Or.inl (Or.inr (Set.mem_singleton_iff.mpr Sym2.eq_swap)))
        · exact Or.inl (Or.inr (Or.inr rfl))
      · rcases hcross y hy x hx hxy.symm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact Or.inl (Or.inl (Or.inr rfl))
        · exact Or.inl (Or.inr (Or.inr (Set.mem_singleton_iff.mpr Sym2.eq_swap)))
      · exact Or.inl (Or.inl (Or.inl ⟨hxy,hx,hy⟩))
    · rintro (((he|he)|(he|he))|he)
      · exact he.1
      · exact (G.adj_congr_of_sym2 he).mpr hua
      · exact P.toSubgraph.edgeSet_subset he
      · exact (G.adj_congr_of_sym2 he).mpr hbv
      · exact C.toSubgraph.edgeSet_subset he

lemma two_terminal_cycle_region {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)}
    (hG : G.Connected) {r u a b v : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hlen : 5 ≤ C.length) (P : G.Walk a b) (hP : P.IsPath)
    (hPS : ∀ x ∈ P.support, x ∈ C.support)
    (hua : G.Adj u a) (hbv : G.Adj b v)
    (hu : u ∉ C.support) (hv : v ∉ C.support) (huv : u ≠ v)
    (hd : Disjoint P.toSubgraph.edgeSet C.toSubgraph.edgeSet)
    (hinside : (within G {x | x ∈ C.support}).edgeSet=P.toSubgraph.edgeSet ∪ C.toSubgraph.edgeSet)
    (hcross : ∀ x ∈ C.support, ∀ y ∉ C.support, G.Adj x y → (x=a ∧ y=u) ∨ (x=b ∧ y=v)) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  have hvP : v ∉ P.support := fun hh ↦ hv (hPS v hh)
  apply cycle_corridor_budget hsmall hG C hC hlen (hPS a P.start_mem_support) hu hv huv
    (P.concat hbv) (hP.concat hvP hbv)
  · intro x hx
    have hh : x ∈ P.support ∨ x=v := by simpa only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] using hx
    exact hh.elim (fun hh ↦ Or.inl (hPS x hh)) Or.inr
  · apply Set.disjoint_left.mpr
    intro e he hc
    have he' : e ∈ P.toSubgraph.edgeSet ∨ e=s(b,v) := by
      simpa only [Walk.edgeSet_toSubgraph,Set.mem_setOf_eq,Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] using he
    rcases he' with he|rfl
    · exact Set.disjoint_left.mp hd he hc
    · exact hv (Walk.mem_support_of_adj_toSubgraph (C.toSubgraph.symm hc))
  · exact two_terminal_cycle_cover C P hua hbv hu hv hinside hcross

lemma carrier_trace {r s t u a b v : V} (C : G.Walk r r)
    (L : G.Walk s u) (P : G.Walk a b) (B : G.Walk v t)
    (hua : G.Adj u a) (hbv : G.Adj b v)
    (hL : ∀ x ∈ L.support, x ∉ C.support) (hB : ∀ x ∈ B.support, x ∉ C.support)
    (hcarrier : ∀ x ∈ C.support, ∀ y, G.Adj x y → C.toSubgraph.Adj x y ∨
      (L.append (Walk.cons hua (P.append (Walk.cons hbv B)))).toSubgraph.Adj x y)
    {x y : V} (hx : x ∈ C.support) (hxy : G.Adj x y) :
    C.toSubgraph.Adj x y ∨ P.toSubgraph.Adj x y ∨ (x=a ∧ y=u) ∨ (x=b ∧ y=v) := by
  rcases hcarrier x hx y hxy with hc|hw
  · exact Or.inl hc
  change s(x,y) ∈ (L.append (Walk.cons hua (P.append (Walk.cons hbv B)))).toSubgraph.edgeSet at hw
  have he : s(x,y) ∈ L.toSubgraph.edgeSet ∨ s(x,y)=s(u,a) ∨
      s(x,y) ∈ P.toSubgraph.edgeSet ∨ s(x,y)=s(b,v) ∨ s(x,y) ∈ B.toSubgraph.edgeSet := by
    simpa only [Walk.edgeSet_toSubgraph,Set.mem_setOf_eq,Walk.edges_append,Walk.edges_cons,
      List.mem_append,List.mem_cons] using hw
  rcases he with he|he|he|he|he
  · exact (hL x (Walk.mem_support_of_adj_toSubgraph he) hx).elim
  · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (hL _ L.end_mem_support hx).elim
    · exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))
  · exact Or.inr (Or.inl he)
  · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))
    · exact (hB _ B.start_mem_support hx).elim
  · exact (hB x (Walk.mem_support_of_adj_toSubgraph he) hx).elim

lemma single_carrier_cycle_region {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)}
    (hG : G.Connected) {r s t u a b v : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hlen : 5 ≤ C.length) (L : G.Walk s u) (P : G.Walk a b) (B : G.Walk v t)
    (hua : G.Adj u a) (hbv : G.Adj b v)
    (hW : (L.append (Walk.cons hua (P.append (Walk.cons hbv B)))).IsPath)
    (hL : ∀ x ∈ L.support, x ∉ C.support) (hB : ∀ x ∈ B.support, x ∉ C.support)
    (hP : ∀ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint (L.append (Walk.cons hua (P.append (Walk.cons hbv B)))).toSubgraph.edgeSet
      C.toSubgraph.edgeSet)
    (hcarrier : ∀ x ∈ C.support, ∀ y, G.Adj x y → C.toSubgraph.Adj x y ∨
      (L.append (Walk.cons hua (P.append (Walk.cons hbv B)))).toSubgraph.Adj x y) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  have hu := hL u L.end_mem_support
  have hv := hB v B.start_mem_support
  have huv : u ≠ v := by
    intro he
    have hh := (Walk.cons_isPath_iff hua _).mp hW.of_append_right |>.2
    apply hh
    rw [he,Walk.mem_support_append_iff]
    exact Or.inr (List.mem_cons_of_mem _ B.start_mem_support)
  have hPP := hW.of_append_right.of_cons.of_append_left
  have hdP : Disjoint P.toSubgraph.edgeSet C.toSubgraph.edgeSet := by
    apply hd.mono_left
    intro e he
    simp only [Walk.edgeSet_toSubgraph,Set.mem_setOf_eq,Walk.edges_append,Walk.edges_cons,
      List.mem_append,List.mem_cons] at he ⊢
    exact Or.inr (Or.inr (Or.inl he))
  apply two_terminal_cycle_region hsmall hG C hC hlen P hPP hP hua hbv hu hv huv hdP
  · ext e
    induction e using Sym2.ind with
    | h x y =>
      constructor
      · rintro ⟨hxy,hx,hy⟩
        rcases carrier_trace C L P B hua hbv hL hB hcarrier hx hxy with hc|hp|⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact Or.inr hc
        · exact Or.inl hp
        · exact (hu hy).elim
        · exact (hv hy).elim
      · rintro (hp|hc)
        · exact ⟨P.toSubgraph.adj_sub hp,hP x (Walk.mem_support_of_adj_toSubgraph hp),
            hP y (Walk.mem_support_of_adj_toSubgraph (P.toSubgraph.symm hp))⟩
        · exact ⟨C.toSubgraph.adj_sub hc,Walk.mem_support_of_adj_toSubgraph hc,
            Walk.mem_support_of_adj_toSubgraph (C.toSubgraph.symm hc)⟩
  · intro x hx y hy hxy
    rcases carrier_trace C L P B hua hbv hL hB hcarrier hx hxy with hc|hp|hu'|hv'
    · exact (hy (Walk.mem_support_of_adj_toSubgraph (C.toSubgraph.symm hc))).elim
    · exact (hy (hP y (Walk.mem_support_of_adj_toSubgraph (P.toSubgraph.symm hp)))).elim
    · exact Or.inl hu'
    · exact Or.inr hv'

lemma failure_no_single_contiguous_carrier {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : QuotaTrails.TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : QuotaTrails.TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    {r u a b v : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (L : G.Walk (T.start j) u) (P : G.Walk a b) (B : G.Walk v (T.finish j))
    (hua : G.Adj u a) (hbv : G.Adj b v)
    (hj : T.walk j=L.append (Walk.cons hua (P.append (Walk.cons hbv B))))
    (hL : ∀ x ∈ L.support, x ∉ C.support) (hB : ∀ x ∈ B.support, x ∉ C.support)
    (hP : ∀ x ∈ P.support, x ∈ C.support)
    (hother : ∀ l, l ≠ i → l ≠ j → ∀ x ∈ (T.walk l).support, x ∉ C.support) : False := by
  have hb : Fintype.card (Fin n) ≤ 2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,ceil_half]
    omega
  have hlen := QuadrilateralAbsorption.whole_cycle_length_ge_five T hG hs hm hb i C hC hi
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  have hpj := (T.one_defect_other_paths hs i hnp).2 j hij.symm
  apply hfail
  apply single_carrier_cycle_region hsmall hG C hC hlen L P B hua hbv (hj ▸ hpj) hL hB hP
  · rw [←hj,←hi]
    exact T.disjoint hij.symm
  · intro x hx y hxy
    obtain ⟨l,hl⟩ := (T.cover s(x,y)).mp hxy
    by_cases hli : l=i
    · subst l
      exact Or.inl (hi ▸ hl)
    · by_cases hlj : l=j
      · subst l
        exact Or.inr ((congrArg Walk.toSubgraph hj) ▸ hl)
      · exact (hother l hli hlj x (Walk.mem_support_of_adj_toSubgraph hl) hx).elim

lemma deleted_subgraph_corridor_budget {n q : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (K : G.Subgraph)
    (hF : (G.deleteEdges K.edgeSet).Connected)
    (S : Set (Fin n)) {u a v : Fin n}
    (ha : a ∈ S) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (R : (G.deleteEdges K.edgeSet).Walk a v) (hpR : R.IsPath)
    (hR : ∀ x ∈ R.support, x ∈ S ∨ x=v)
    (hc : (G.deleteEdges K.edgeSet).edgeSet =
      ((within (G.deleteEdges K.edgeSet) Sᶜ).edgeSet ∪ {s(u,a)}) ∪ R.toSubgraph.edgeSet)
    (A : Finset G.Subgraph) (hA : ∀ J ∈ A, IsPathSubgraph J)
    (hdA : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun J ↦ J.edgeSet))
    (hcA : (⋃ J ∈ A, J.edgeSet)=K.edgeSet) (hAc : A.card ≤ q)
    (hq : 0 < q) (hsize : 2*q+1 ≤ S.ncard) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let F := G.deleteEdges K.edgeSet
  have hc' : F.edgeSet = ((within F Sᶜ).edgeSet ∪ {s(u,a)}) ∪ R.toSubgraph.edgeSet ∪
      (⊥ : F.Subgraph).edgeSet := by simpa only [Subgraph.edgeSet_bot,Set.union_empty] using hc
  have hconn := proxy_connected S hF ha hu hv huv R hR (⊥ : F.Subgraph) (by simp) hc'
  have hs := Set.ncard_mono (proxy_support_subset (G := F) (a := a) S hu hv)
  have hsum : S.ncard+Sᶜ.ncard=n := by simpa using S.ncard_add_ncard_compl
  have hcount : (proxy F S u a v).support.ncard+2*q ≤ n := by
    have hi := Set.ncard_insert_le a Sᶜ
    omega
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall
    (proxy F S u a v) hconn (by omega)
  obtain ⟨D',hD',hD'c⟩ := restore_proxy_corridor S ha hu hv huv R hpR hR (⊥ : F.Subgraph)
    (by simp) (by simp) hc' ∅ (by simp) (by simp [Set.PairwiseDisjoint]) (by simp) hD
  obtain ⟨E,hE,hEc⟩ := restore_partitioned_subgraph K A hA hdA hcA hD'
  refine ⟨E,hE,?_⟩
  simp only [Finset.card_empty,add_zero] at hD'c
  rw [ceil_half] at hDc
  simp only [Fintype.card_fin,ceil_half]
  omega

lemma deleted_cycle_corridor_budget {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r u a v : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hF : (G.deleteEdges C.toSubgraph.edgeSet).Connected)
    (S : Set (Fin n)) (ha : a ∈ S) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (R : (G.deleteEdges C.toSubgraph.edgeSet).Walk a v) (hpR : R.IsPath)
    (hR : ∀ x ∈ R.support, x ∈ S ∨ x=v)
    (hc : (G.deleteEdges C.toSubgraph.edgeSet).edgeSet =
      ((within (G.deleteEdges C.toSubgraph.edgeSet) Sᶜ).edgeSet ∪ {s(u,a)}) ∪ R.toSubgraph.edgeSet)
    (hsize : 5 ≤ S.ncard) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  obtain ⟨A,hA,hdA,hAc,hAs⟩ := MemberNormalExpansion.two_path_parts (cycle_two_path_cover C hC)
  exact deleted_subgraph_corridor_budget (q := 2) hsmall C.toSubgraph hF S ha hu hv huv
    R hpR hR hc A hA hdA hAc hAs (by decide) hsize

end Erdos583CorridorReductionDevelopment
