import Submission.Work

/-! Two-leaf reductions for a smallest-order path-decomposition failure.
The reductions use an edge expansion and a one-edge deletion, not unrestricted
marked-endpoint flexibility. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
namespace Erdos583LeafPairReductionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma leaf_data {V : Type*} [Fintype V] {G : SimpleGraph V} {u : V}
    (hu : Nat.card (G.neighborSet u)=1) :
    ∃ a, G.Adj u a ∧ ∀ x, G.Adj u x → x=a := by
  rw [Nat.card_coe_set_eq] at hu
  obtain ⟨a,ha⟩ := Set.ncard_eq_one.mp hu
  exact ⟨a,by change a ∈ G.neighborSet u; rw [ha]; exact rfl,
    fun x hx ↦ (ha ▸ hx : x ∈ ({a} : Set V))⟩

lemma delete_two_leaves_connected {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {u v a b : V} (ha : G.Adj u a) (hav : a ≠ v)
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=b) :
    (G.induce ({u,v}ᶜ : Set V)).Connected := by
  letI : Nonempty ↥({u,v}ᶜ : Set V) := ⟨⟨a,by simp [ha.ne.symm,hav]⟩⟩
  refine ⟨hG.preconnected.induce_of_degree_eq_one ?_⟩
  intro x hx y hy z hz
  have hx' : x=u ∨ x=v := by simpa only [Set.mem_compl_iff,not_not,Set.mem_insert_iff,Set.mem_singleton_iff] using hx
  rcases hx' with rfl|rfl
  · exact (hu y hy).trans (hu z hz).symm
  · exact (hv y hy).trans (hv z hz).symm

lemma two_leaves_edge_cover {V : Type*} {G : SimpleGraph V}
    {u v a b : V} (ha : G.Adj u a) (hb : G.Adj v b)
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=b) :
    G.edgeSet=(within G ({u,v}ᶜ : Set V)).edgeSet ∪ {s(u,a),s(v,b)} := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    constructor
    · intro hxy
      by_cases hx : x=u
      · subst x; have hy := hu y hxy; subst y; exact Or.inr (Or.inl rfl)
      by_cases hxv : x=v
      · subst x; have hy := hv y hxy; subst y; exact Or.inr (Or.inr rfl)
      by_cases hy : y=u
      · subst y; have hx := hu x hxy.symm; subst x; exact Or.inr (Or.inl Sym2.eq_swap)
      by_cases hyv : y=v
      · subst y; have hx := hv x hxy.symm; subst x; exact Or.inr (Or.inr Sym2.eq_swap)
      exact Or.inl ⟨hxy,by simp [hx,hxv],by simp [hy,hyv]⟩
    · rintro (h|h)
      · exact h.1
      · rcases h with h|h
        · exact (G.adj_congr_of_sym2 h).mpr ha
        · exact (G.adj_congr_of_sym2 h).mpr hb

lemma two_removed_budget {n c d : ℕ} {u v : Fin n} (huv : u ≠ v)
    (hc : c ≤ ⌈((({u,v}ᶜ : Set (Fin n)).ncard : ℚ)/2)⌉₊) (hd : d ≤ c+1) :
    d ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  have hn : ({u,v}ᶜ : Set (Fin n)).ncard+2=n := by
    have h := (show ({u,v} : Set (Fin n)).ncard+({u,v}ᶜ : Set (Fin n)).ncard=n from by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
        ({u,v} : Set (Fin n)).ncard_add_ncard_compl)
    rw [Set.ncard_pair huv] at h
    omega
  rw [ceil_half] at hc
  simp only [Fintype.card_fin,ceil_half]
  omega

lemma two_removed_lt {n : ℕ} {u v : Fin n} (huv : u ≠ v) :
    ({u,v}ᶜ : Set (Fin n)).ncard < n := by
  have h := ({u,v} : Set (Fin n)).ncard_add_ncard_compl
  rw [Set.ncard_pair huv,Nat.card_eq_fintype_card,Fintype.card_fin] at h
  omega

lemma common_neighbor_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v a : Fin n} (huv : u ≠ v) (ha : G.Adj u a) (hb : G.Adj v a)
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=a) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let P : G.Walk u v := .cons ha (.cons hb.symm .nil)
  have hp : P.IsPath := by simp [P,Walk.cons_isPath_iff,ha.ne,hb.ne.symm,huv]
  have hdel : G.deleteEdges P.toSubgraph.edgeSet=within G ({u,v}ᶜ : Set (Fin n)) := by
    have hc := two_leaves_edge_cover ha hb hu hv
    apply edgeSet_injective
    rw [edgeSet_deleteEdges,hc]
    have hpe : P.toSubgraph.edgeSet={s(u,a),s(v,a)} := by
      ext e; simp [P,Sym2.eq_swap,or_comm]
    rw [hpe]
    rw [Set.union_diff_distrib,Set.diff_self,Set.union_empty]
    apply sdiff_eq_left.mpr
    apply Set.disjoint_left.mpr
    intro e he he'
    rcases he' with he'|he'
    · have he'' : s(u,a) ∈ (within G ({u,v}ᶜ : Set (Fin n))).edgeSet := he' ▸ he
      exact he''.2.1 (Or.inl rfl)
    · have he'' : s(v,a) ∈ (within G ({u,v}ᶜ : Set (Fin n))).edgeSet := he' ▸ he
      exact he''.2.1 (Or.inr rfl)
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G ({u,v}ᶜ : Set (Fin n)) (two_removed_lt huv)
    (delete_two_leaves_connected hG ha hb.ne.symm hu hv)
  have hex := lift_induce_within ({u,v}ᶜ : Set (Fin n)) D hD
  rw [←hdel] at hex
  obtain ⟨E,hE,hEc⟩ := hex
  obtain ⟨F,hF,hFc⟩ := restore_path_subgraph ⟨_,_,P,hp,rfl⟩ hE
  exact ⟨F,hF,two_removed_budget huv hDc (by omega)⟩

lemma leaf_neighbors_nonadjacent_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v a b : Fin n} (huv : u ≠ v) (ha : G.Adj u a) (hb : G.Adj v b)
    (hav : a ≠ v) (hbu : b ≠ u) (hab : a ≠ b) (hnab : ¬G.Adj a b)
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {u,v}ᶜ
  let A := within G S
  let H := A ⊔ fromEdgeSet {s(a,b)}
  let J := G ⊔ fromEdgeSet {s(u,v)}
  have habH : H.Adj a b := Or.inr ⟨rfl,hab⟩
  have huvJ : J.Adj u v := Or.inr ⟨rfl,huv⟩
  have hGJ : G ≤ J := le_sup_left
  have huvn : ¬G.Adj u v := fun h ↦ hav (hu v h).symm
  have hma : a ∈ S := by simp [S,ha.ne.symm,hav]
  have hmb : b ∈ S := by simp [S,hbu,hb.ne.symm]
  have hHe : H.edgeSet=A.edgeSet ∪ {s(a,b)} := by
    change (A ⊔ fromEdgeSet {s(a,b)}).edgeSet=_
    rw [edgeSet_sup,edgeSet_fromEdgeSet]
    congr 1
    apply Set.Subset.antisymm Set.diff_subset
    rintro e rfl
    exact ⟨rfl,fun hd ↦ hab (Sym2.mem_diagSet_iff_eq.mp hd)⟩
  have hJe : J.edgeSet=G.edgeSet ∪ {s(u,v)} := by
    change (G ⊔ fromEdgeSet {s(u,v)}).edgeSet=_
    rw [edgeSet_sup,edgeSet_fromEdgeSet]
    congr 1
    apply Set.Subset.antisymm Set.diff_subset
    rintro e rfl
    exact ⟨rfl,fun hd ↦ huv (Sym2.mem_diagSet_iff_eq.mp hd)⟩
  have hAH : within H S=H := by
    ext x y
    constructor
    · exact And.left
    · rintro (h|h)
      · exact ⟨Or.inl h,h.2⟩
      · obtain ⟨he,_⟩ := h
        rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨habH,hma,hmb⟩
        · exact ⟨habH.symm,hmb,hma⟩
  have hconn : (H.induce S).Connected :=
    (delete_two_leaves_connected hG ha hav hu hv).mono
      (by intro x y h; exact Or.inl ⟨h,x.property,y.property⟩)
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce H S (two_removed_lt huv) hconn
  have hex := lift_induce_within S D hD
  rw [hAH] at hex
  obtain ⟨E,hE,hEc⟩ := hex
  let P : J.Walk a b := .cons (hGJ ha.symm) (.cons huvJ (.cons (hGJ hb) .nil))
  have hp : P.IsPath := by
    simp [P,Walk.cons_isPath_iff,ha.ne.symm,hav,hab,huv,hbu.symm,hb.ne]
  have hfresh : ∀ x ∈ P.support, x ≠ a → x ≠ b → x ∉ H.support := by
    intro x hx hxa hxb hs
    have hx' : x=u ∨ x=v := by simpa [P,hxa,hxb] using hx
    obtain ⟨y,hy⟩ := H.mem_support.mp hs
    have hxS := (show (within H S).Adj x y from hAH.symm ▸ hy).2.1
    rcases hx' with rfl|rfl
    · exact hxS (Or.inl rfl)
    · exact hxS (Or.inr rfl)
  have hc : J.edgeSet=(H.edgeSet \ {s(a,b)}) ∪ P.toSubgraph.edgeSet := by
    have hpe : P.toSubgraph.edgeSet={s(u,a),s(u,v),s(v,b)} := by
      ext e; simp [P,Sym2.eq_swap,or_comm,or_left_comm,or_assoc]
    have hna : s(a,b) ∉ A.edgeSet := fun he ↦ hnab he.1
    rw [hHe,Set.union_diff_distrib,Set.diff_self,Set.union_empty,Set.diff_singleton_eq_self hna,
      hJe,two_leaves_edge_cover ha hb hu hv,hpe]
    ext e
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  obtain ⟨F,hF,hFc⟩ := hE.expand_edge habH P hp hfresh hc
  have hdelete := delete_edge_decomposition hF ⟨s(u,v),huvJ⟩
  have hJG : J.deleteEdges {s(u,v)}=G := by
    apply edgeSet_injective
    rw [edgeSet_deleteEdges,hJe,Set.union_diff_distrib,Set.diff_self,Set.union_empty,
      Set.diff_singleton_eq_self (show s(u,v) ∉ G.edgeSet from huvn)]
  rw [hJG] at hdelete
  obtain ⟨K,hK,hKc⟩ := hdelete
  exact ⟨K,hK,two_removed_budget huv hDc (by omega)⟩


lemma leaf_neighbors_nonbridge_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v a b : Fin n} (huv : u ≠ v) (ha : G.Adj u a) (hb : G.Adj v b)
    (hav : a ≠ v) (hbu : b ≠ u) (hab : G.Adj a b) (hnb : ¬G.IsBridge s(a,b))
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let J := G.deleteEdges {s(a,b)}
  let S : Set (Fin n) := {u,v}ᶜ
  let P : G.Walk u v := .cons ha (.cons hab (.cons hb.symm .nil))
  have hp : P.IsPath := by
    simp [P,Walk.cons_isPath_iff,ha.ne,hb.ne.symm,huv,hav,hab.ne,hbu.symm]
  have hJa : J.Adj u a := by
    exact ⟨ha,by simp [ha.ne,hbu.symm]⟩
  have hJb : J.Adj v b := by
    exact ⟨hb,by simp [hav.symm,hb.ne]⟩
  have hconn : (J.induce S).Connected := delete_two_leaves_connected
    (hG.connected_delete_edge_of_not_isBridge hnb) hJa hav
    (fun x hx ↦ hu x hx.1) (fun x hx ↦ hv x hx.1)
  have hdel : G.deleteEdges P.toSubgraph.edgeSet=within J S := by
    ext x y
    have hpe : s(x,y) ∈ P.toSubgraph.edgeSet ↔
        s(x,y)=s(u,a) ∨ s(x,y)=s(a,b) ∨ s(x,y)=s(v,b) := by
      simp [P,Sym2.eq_swap,or_comm,or_left_comm]
    constructor
    · intro hxy
      obtain ⟨hxy,hn⟩ := deleteEdges_adj.mp hxy
      rw [hpe] at hn
      refine ⟨deleteEdges_adj.mpr ⟨hxy,fun he ↦ hn (Or.inr (Or.inl he))⟩,?_,?_⟩
      · rintro (hx|hx)
        · subst x; have he := hu y hxy; subst y; exact hn (Or.inl rfl)
        · have hx' : x=v := hx
          subst x; have he := hv y hxy; subst y; exact hn (Or.inr (Or.inr rfl))
      · rintro (hy|hy)
        · subst y; have he := hu x hxy.symm; subst x; exact hn (Or.inl Sym2.eq_swap)
        · have hy' : y=v := hy
          subst y; have he := hv x hxy.symm; subst x; exact hn (Or.inr (Or.inr Sym2.eq_swap))
    · intro hxy
      apply deleteEdges_adj.mpr
      refine ⟨hxy.1.1,?_⟩
      rw [hpe]
      rintro (he|he|he)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hxy.2.1 (Or.inl rfl)
        · exact hxy.2.2 (Or.inl rfl)
      · exact (deleteEdges_adj.mp hxy.1).2 he
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hxy.2.1 (Or.inr rfl)
        · exact hxy.2.2 (Or.inr rfl)
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce J S (two_removed_lt huv) hconn
  have hex := lift_induce_within S D hD
  rw [←hdel] at hex
  obtain ⟨E,hE,hEc⟩ := hex
  obtain ⟨F,hF,hFc⟩ := restore_path_subgraph ⟨_,_,P,hp,rfl⟩ hE
  exact ⟨F,hF,two_removed_budget huv hDc (by omega)⟩

lemma leaf_neighbor_not_leaf_of_failure {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    {u a : V} (ha : G.Adj u a) (hu : ∀ x, G.Adj u x → x=a) :
    Nat.card (G.neighborSet a) ≠ 1 := by
  intro hla
  obtain ⟨b,hb,ha'⟩ := leaf_data hla
  have hbu : b=u := (ha' u ha.symm).symm
  subst b
  have hV (x : V) : x=u ∨ x=a := by
    have hm : x ∈ ({u,a} : Set V) := reachable_mem_of_closed
      (T := {u,a}) (fun y hy z hyz ↦ ?_) (hG.preconnected u x) (Or.inl rfl)
    · exact hm
    · rcases hy with hy|hy
      · subst y; exact Or.inr (hu z hyz)
      · have hy' : y=a := hy
        subst y; exact Or.inl (ha' z hyz)
  have hd (x : V) : Nat.card (G.neighborSet x) ≤ 3 := by
    rcases hV x with hx|hx
    · subst x
      have he : G.neighborSet u={a} := by ext y; exact ⟨hu y,fun h ↦ h ▸ ha⟩
      rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]; omega
    · subst x; omega
  obtain ⟨D,hD,hDc⟩ := subcubic_erdos_583 G hG hd
  exact hfail ⟨D,hD,hDc⟩

/-- In a smallest failure two distinct leaves have distinct neighbors, and
those neighbors are joined by a bridge. -/
lemma leaf_neighbors_bridge_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v a b : Fin n} (huv : u ≠ v) (ha : G.Adj u a) (hb : G.Adj v b)
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=b) :
    a ≠ b ∧ G.IsBridge s(a,b) := by
  classical
  have hla : Nat.card (G.neighborSet a) ≠ 1 := leaf_neighbor_not_leaf_of_failure hG hfail ha hu
  have hlb : Nat.card (G.neighborSet b) ≠ 1 := leaf_neighbor_not_leaf_of_failure hG hfail hb hv
  have hdu : Nat.card (G.neighborSet u)=1 := by
    have he : G.neighborSet u={a} := by ext x; exact ⟨hu x,fun h ↦ h ▸ ha⟩
    rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]
  have hdv : Nat.card (G.neighborSet v)=1 := by
    have he : G.neighborSet v={b} := by ext x; exact ⟨hv x,fun h ↦ h ▸ hb⟩
    rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]
  have hav : a ≠ v := fun h ↦ hla (h ▸ hdv)
  have hbu : b ≠ u := fun h ↦ hlb (h ▸ hdu)
  have hab : a ≠ b := by
    intro he
    subst b
    exact hfail (common_neighbor_reduction hsmall hG huv ha hb hu hv)
  have hadj : G.Adj a b := by
    by_contra hn
    exact hfail (leaf_neighbors_nonadjacent_reduction hsmall hG huv ha hb hav hbu hab hn hu hv)
  refine ⟨hab,?_⟩
  by_contra hn
  exact hfail (leaf_neighbors_nonbridge_reduction hsmall hG huv ha hb hav hbu hadj hn hu hv)

/-- A smallest-order failure has at most two leaves, in either order parity. -/
lemma at_most_two_leaves_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) :
    (Finset.univ.filter fun u ↦ Nat.card (G.neighborSet u)=1).card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨u,hu,v,hv,w,hw,huv,huw,hvw⟩ := Finset.two_lt_card.mp (by omega :
    2 < (Finset.univ.filter fun u ↦ Nat.card (G.neighborSet u)=1).card)
  obtain ⟨a,ha,hu'⟩ := leaf_data (Finset.mem_filter.mp hu).2
  obtain ⟨b,hb,hv'⟩ := leaf_data (Finset.mem_filter.mp hv).2
  obtain ⟨c,hc,hw'⟩ := leaf_data (Finset.mem_filter.mp hw).2
  have hab := leaf_neighbors_bridge_of_failure hsmall hG hfail huv ha hb hu' hv'
  have hac := leaf_neighbors_bridge_of_failure hsmall hG hfail huw ha hc hu' hw'
  have hbc := leaf_neighbors_bridge_of_failure hsmall hG hfail hvw hb hc hv' hw'
  exact DegreeThreeReduction.edge_with_common_neighbor_not_bridge
    (isBridge_iff.mp hac.2).1 (isBridge_iff.mp hbc.2).1.symm hab.2

end Erdos583LeafPairReductionDevelopment
