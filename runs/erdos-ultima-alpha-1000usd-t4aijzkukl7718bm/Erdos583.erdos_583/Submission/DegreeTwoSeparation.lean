import Submission.Work

/-! Separation of degree-two triangles in a smallest failure. A nonbridge
edge between two disjoint triangles permits a two-vertex, one-path reduction. -/
namespace Erdos583DegreeTwoSeparationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

lemma delete_two_simplicial_connected {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {u v a b c d : V}
    (huv : u ≠ v) (hab : G.Adj a b) (hcd : G.Adj c d)
    (ha : a ∈ ({u,v}ᶜ : Set V)) (hb : b ∈ ({u,v}ᶜ : Set V))
    (hc : c ∈ ({u,v}ᶜ : Set V)) (hd : d ∈ ({u,v}ᶜ : Set V))
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hNv : ∀ z, G.Adj v z → z=c ∨ z=d) :
    (G.induce ({u,v}ᶜ : Set V)).Connected := by
  classical
  let S : Set V := {u,v}ᶜ
  let f : V → S := fun x ↦ if hx : x=u then ⟨a,ha⟩ else
    if hxv : x=v then ⟨c,hc⟩ else ⟨x,by simp [S,hx,hxv]⟩
  have hfu : f u=⟨a,ha⟩ := by simp [f]
  have hfv : f v=⟨c,hc⟩ := by simp [f,huv.symm]
  have hfs (x : V) (hx : x ∈ S) : f x=⟨x,hx⟩ := by
    have hx' : x ≠ u ∧ x ≠ v := by simpa [S] using hx
    simp [f,hx'.1,hx'.2]
  have hru (y : V) (huy : G.Adj u y) :
      (G.induce S).Reachable (f u) (f y) := by
    rcases hNu y huy with hy|hy
    · subst y
      rw [hfu,hfs a ha]
    · subst y
      rw [hfu,hfs b hb]; exact Adj.reachable hab
  have hrv (y : V) (hvy : G.Adj v y) :
      (G.induce S).Reachable (f v) (f y) := by
    rcases hNv y hvy with hy|hy
    · subst y
      rw [hfv,hfs c hc]
    · subst y
      rw [hfv,hfs d hd]; exact Adj.reachable hcd
  have hf : ∀ x y, G.Adj x y → (G.induce S).Reachable (f x) (f y) := by
    intro x y hxy
    by_cases hxu : x=u
    · subst x; exact hru y hxy
    by_cases hxv : x=v
    · subst x; exact hrv y hxy
    by_cases hyu : y=u
    · subst y; exact (hru x hxy.symm).symm
    by_cases hyv : y=v
    · subst y; exact (hrv x hxy.symm).symm
    rw [hfs x (by simp [S,hxu,hxv]),hfs y (by simp [S,hyu,hyv])]
    exact Adj.reachable hxy
  letI : Nonempty S := ⟨⟨a,ha⟩⟩
  refine ⟨fun x y ↦ ?_⟩
  have hh := reachable_map_to_reachable f hf (hG.preconnected x.val y.val)
  simpa only [hfs x.val x.property,hfs y.val y.property] using hh

lemma disjoint_tips_edge_diff {V : Type*} {G : SimpleGraph V} {u v a b c d : V}
    (hua : G.Adj u a) (hub : G.Adj u b) (hvc : G.Adj v c) (hvd : G.Adj v d)
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hNv : ∀ z, G.Adj v z → z=c ∨ z=d) :
    G.edgeSet \ (within G ({u,v}ᶜ : Set V)).edgeSet =
      {s(u,a),s(u,b),s(v,c),s(v,d)} := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    constructor
    · rintro ⟨hxy,hn⟩
      by_cases hx : x=u
      · subst x; rcases hNu y hxy with rfl|rfl <;> simp
      by_cases hxv : x=v
      · subst x; rcases hNv y hxy with rfl|rfl <;> simp
      by_cases hy : y=u
      · subst y; rcases hNu x hxy.symm with rfl|rfl <;> simp [Sym2.eq_swap]
      by_cases hyv : y=v
      · subst y; rcases hNv x hxy.symm with rfl|rfl <;> simp [Sym2.eq_swap]
      exact (hn ⟨hxy,by simp [hx,hxv],by simp [hy,hyv]⟩).elim
    · intro he
      have he' : s(x,y)=s(u,a) ∨ s(x,y)=s(u,b) ∨ s(x,y)=s(v,c) ∨ s(x,y)=s(v,d) := he
      rcases he' with he|he|he|he <;> rw [he]
      · exact ⟨hua,fun h ↦ h.2.1 (Or.inl rfl)⟩
      · exact ⟨hub,fun h ↦ h.2.1 (Or.inl rfl)⟩
      · exact ⟨hvc,fun h ↦ h.2.1 (Or.inr rfl)⟩
      · exact ⟨hvd,fun h ↦ h.2.1 (Or.inr rfl)⟩

lemma nonbridge_between_tips_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {u v a b c d : Fin n}
    (hnd : [b,u,a,c,v,d].Nodup)
    (hua : G.Adj u a) (hub : G.Adj u b) (hvc : G.Adj v c) (hvd : G.Adj v d)
    (hab : G.Adj a b) (hcd : G.Adj c d) (hac : G.Adj a c)
    (hnb : ¬G.IsBridge s(a,c))
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hNv : ∀ z, G.Adj v z → z=c ∨ z=d) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  have hneq := hnd
  simp only [List.nodup_cons,List.mem_cons,not_or,List.nodup_nil,
    List.not_mem_nil,not_false_eq_true,and_true] at hneq
  have huv : u ≠ v := by tauto
  let J := G.deleteEdges {s(a,c)}
  let S : Set (Fin n) := {u,v}ᶜ
  let H := within J S
  have hJG : J ≤ G := G.deleteEdges_le _
  have habJ : J.Adj a b := by
    apply deleteEdges_adj.mpr
    refine ⟨hab,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq_iff]
    grind
  have hcdJ : J.Adj c d := by
    apply deleteEdges_adj.mpr
    refine ⟨hcd,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq_iff]
    grind
  have hcJ : (J.induce S).Connected :=
    delete_two_simplicial_connected (hG.connected_delete_edge_of_not_isBridge hnb)
      huv habJ hcdJ (by simp only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff]; grind)
      (by simp only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff]; grind)
      (by simp only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff]; grind)
      (by simp only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff]; grind)
      (fun z h ↦ hNu z (hJG h)) (fun z h ↦ hNv z (hJG h))
  let P : G.Walk b d := .cons hub.symm (.cons hua (.cons hac (.cons hvc.symm (.cons hvd .nil))))
  have hp : P.IsPath := by apply Walk.IsPath.mk'; simpa [P] using hnd
  have hpe : P.toSubgraph.edgeSet=(G.edgeSet \ (within G S).edgeSet) ∪ {s(a,c)} := by
    rw [disjoint_tips_edge_diff hua hub hvc hvd hNu hNv]
    ext e
    simp only [P,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false,Set.mem_union,Set.mem_insert_iff,
      Set.mem_singleton_iff,Sym2.eq_swap (a := b) (b := u),Sym2.eq_swap (a := c) (b := v)]
    tauto
  have hdel : G.deleteEdges P.toSubgraph.edgeSet=H := by
    apply edgeSet_injective
    rw [edgeSet_deleteEdges,hpe]
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [H,J,Set.mem_diff,Set.mem_union,mem_edgeSet,within,deleteEdges_adj,Set.mem_singleton_iff]
      tauto
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce J S (LeafPairReduction.two_removed_lt huv) hcJ
  have hex := lift_induce_within S D hD
  rw [show within J S=H from rfl,←hdel] at hex
  obtain ⟨E,hE,hEc⟩ := hex
  obtain ⟨F,hF,hFc⟩ := restore_path_subgraph ⟨_,_,P,hp,rfl⟩ hE
  exact ⟨F,hF,LeafPairReduction.two_removed_budget huv hDc (by omega)⟩

/-- An edge joining neighbors of distinct degree-two vertices in a smallest
failure must be a bridge. The closed-neighborhood disjointness is essential
for the five-edge restoring walk to be a path. -/
lemma degree_two_cross_edge_bridge {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v a c : Fin n} (huv : u ≠ v)
    (hu : Nat.card (G.neighborSet u)=2) (hv : Nat.card (G.neighborSet v)=2)
    (hua : G.Adj u a) (hvc : G.Adj v c) (hac : G.Adj a c) :
    G.IsBridge s(a,c) := by
  by_contra hnb
  obtain ⟨b,hub,hab,hNu⟩ := DegreeTwoPacking.degree_two_triangle_at_neighbor hsmall hG hfail hua hu
  obtain ⟨d,hvd,hcd,hNv⟩ := DegreeTwoPacking.degree_two_triangle_at_neighbor hsmall hG hfail hvc hv
  have hsep := DegreeTwoPacking.degree_two_closed_neighbors_disjoint hsmall hG hfail huv hu hv
  have hnd : [b,u,a,c,v,d].Nodup := by
    change ([b,u,a]++[c,v,d]).Nodup
    rw [List.nodup_append]
    refine ⟨by simp [hub.ne.symm,hab.ne.symm,hua.ne],
      by simp [hvc.ne.symm,hcd.ne,hvd.ne],?_⟩
    intro x hx y hy hxy
    subst y
    have hxu : x ∈ insert u (G.neighborSet u) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hx|hx|hx
      · exact Or.inr (hx ▸ hub)
      · exact Or.inl hx
      · exact Or.inr (hx ▸ hua)
    have hxv : x ∈ insert v (G.neighborSet v) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with hy|hy|hy
      · exact Or.inr (hy ▸ hvc)
      · exact Or.inl hy
      · exact Or.inr (hy ▸ hvd)
    exact Set.disjoint_left.mp hsep hxu hxv
  exact hfail (nonbridge_between_tips_reduction hsmall hG hnd hua hub hvc hvd hab hcd hac hnb hNu hNv)

lemma degree_two_cross_edge_large_odd {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v a c : Fin n} (huv : u ≠ v)
    (hu : Nat.card (G.neighborSet u)=2) (hv : Nat.card (G.neighborSet v)=2)
    (hua : G.Adj u a) (hvc : G.Adj v c) (hac : G.Adj a c) :
    Odd (Nat.card (G.neighborSet a)) ∧ Odd (Nat.card (G.neighborSet c)) ∧
      5 ≤ Nat.card (G.neighborSet a) ∧ 5 ≤ Nat.card (G.neighborSet c) := by
  have hb := degree_two_cross_edge_bridge hsmall hG hfail huv hu hv hua hvc hac
  obtain ⟨hoa,hoc⟩ := BridgeParityReduction.bridge_endpoints_odd_of_failure hsmall hG hfail hb
  have hda := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hua hu
  have hdc := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hvc hv
  refine ⟨hoa,hoc,?_,?_⟩
  · obtain ⟨m,hm⟩ := hoa; omega
  · obtain ⟨m,hm⟩ := hoc; omega

/-- Vertices in a closed neighborhood of some degree-two vertex. -/
def tipRegion {V : Type*} (G : SimpleGraph V) : Set V :=
  {x | ∃ u, Nat.card (G.neighborSet u)=2 ∧ x ∈ insert u (G.neighborSet u)}

lemma tipRegion_card {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) :
    (tipRegion G).ncard=3*{u | Nat.card (G.neighborSet u)=2}.ncard := by
  classical
  let I := {u | Nat.card (G.neighborSet u)=2}.toFinset
  let B := fun u ↦ (insert u (G.neighborSet u)).toFinset
  have hI : I.card={u | Nat.card (G.neighborSet u)=2}.ncard := by
    simp only [I,Set.toFinset_card,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hB : ∀ u ∈ I, (B u).card=3 := by
    intro u hu
    have hu' : Nat.card (G.neighborSet u)=2 := by simpa [I] using hu
    have hnot : u ∉ G.neighborSet u := G.irrefl
    change (insert u (G.neighborSet u)).toFinset.card=3
    rw [Set.toFinset_insert,Finset.card_insert_of_notMem (fun h ↦ hnot (Set.mem_toFinset.mp h)),Set.toFinset_card]
    rw [←Nat.card_eq_fintype_card,hu']
  have hdis : (I : Set (Fin n)).PairwiseDisjoint B := by
    intro u hu v hv huv
    have hu' : Nat.card (G.neighborSet u)=2 := by simpa [I] using hu
    have hv' : Nat.card (G.neighborSet v)=2 := by simpa [I] using hv
    apply Finset.disjoint_left.mpr
    intro a hau hav
    exact Set.disjoint_left.mp (DegreeTwoPacking.degree_two_closed_neighbors_disjoint hsmall hG hfail huv hu' hv')
      (Set.mem_toFinset.mp hau) (Set.mem_toFinset.mp hav)
  have hR : (tipRegion G).toFinset=I.biUnion B := by
    ext x
    simp [tipRegion,I,B]
  have hRc : (tipRegion G).ncard=(tipRegion G).toFinset.card := by
    simp only [Set.toFinset_card,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  rw [hRc,hR,Finset.card_biUnion hdis,Finset.sum_const_nat hB,hI,Nat.mul_comm]

lemma edge_to_other_tip_region {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u a x : Fin n} (hu : Nat.card (G.neighborSet u)=2)
    (hua : G.Adj u a) (hax : G.Adj a x)
    (hx : x ∈ tipRegion G) (hxu : x ∉ insert u (G.neighborSet u)) :
    G.IsBridge s(a,x) ∧ 4 ≤ Nat.card (G.neighborSet x) := by
  obtain ⟨v,hv,hxv⟩ := hx
  have huv : u ≠ v := by
    rintro rfl
    exact hxu hxv
  rcases hxv with h|h
  · subst x
    exact (Set.disjoint_left.mp (DegreeTwoPacking.degree_two_neighbors_disjoint hsmall hG hfail huv hu hv)
      hua hax.symm).elim
  · exact ⟨degree_two_cross_edge_bridge hsmall hG hfail huv hu hv hua h hax,
      LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail h hv⟩

/-- At least one of the two neighbors of a degree-two vertex has no edge
into any other degree-two closed neighborhood. Otherwise there would be two
distinct non-leaf bridges. -/
lemma one_neighbor_has_no_cross_edge {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u a b : Fin n} (hu : Nat.card (G.neighborSet u)=2)
    (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b) :
    (∀ x, G.Adj a x → x ∈ tipRegion G → x ∈ insert u (G.neighborSet u)) ∨
    (∀ x, G.Adj b x → x ∈ tipRegion G → x ∈ insert u (G.neighborSet u)) := by
  classical
  by_cases ha : ∀ x, G.Adj a x → x ∈ tipRegion G → x ∈ insert u (G.neighborSet u)
  · exact Or.inl ha
  push_neg at ha
  obtain ⟨x,hax,hx,hxu⟩ := ha
  obtain ⟨hbrx,hdx⟩ := edge_to_other_tip_region hsmall hG hfail hu hua hax hx hxu
  have hda := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hua hu
  have hdb := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hub hu
  refine Or.inr (fun y hby hy ↦ ?_)
  by_contra hyu
  obtain ⟨hbry,hdy⟩ := edge_to_other_tip_region hsmall hG hfail hu hub hby hy hyu
  have he := BalancedBridge.nonleaf_bridge_unique_of_failure hsmall hG hfail hbrx hbry
    (by omega) (by omega) (by omega) (by omega)
  rcases Sym2.eq_iff.mp he with ⟨he,_⟩|⟨_,he⟩
  · exact hab he
  · exact hxu (Or.inr (he ▸ hub))

lemma two_outside_tip_region_of_clean_neighbor {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u a b : Fin n} (hu : Nat.card (G.neighborSet u)=2)
    (hua : G.Adj u a) (hub : G.Adj u b)
    (hNu : ∀ z, G.Adj u z → z=a ∨ z=b)
    (hclean : ∀ x, G.Adj a x → x ∈ tipRegion G → x ∈ insert u (G.neighborSet u)) :
    2 ≤ (tipRegion G)ᶜ.ncard := by
  have hsub : G.neighborSet a ∩ tipRegion G ⊆ ({u,b} : Set (Fin n)) := by
    rintro z ⟨haz,hzR⟩
    rcases hclean z haz hzR with hzu|huz
    · exact Or.inl hzu
    · rcases hNu z huz with hza|hzb
      · exact (haz.ne hza.symm).elim
      · exact Or.inr hzb
  have hi : (G.neighborSet a ∩ tipRegion G).ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hub.ne)
  have hd := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hua hu
  rw [Nat.card_coe_set_eq] at hd
  have hsum := Set.ncard_inter_add_ncard_diff_eq_ncard (G.neighborSet a) (tipRegion G)
  have hc := Set.ncard_le_ncard (show G.neighborSet a \ tipRegion G ⊆ (tipRegion G)ᶜ from fun _ h ↦ h.2)
  omega

/-- At least two vertices of a smallest failure lie outside every degree-two
closed neighborhood. This improves the previous disjoint-triple count. -/
lemma two_outside_tip_region {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) :
    2 ≤ (tipRegion G)ᶜ.ncard := by
  classical
  by_cases hex : ∃ u, Nat.card (G.neighborSet u)=2
  · obtain ⟨u,hu⟩ := hex
    obtain ⟨_,a,b,hab,hN,habG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hu
    have hua : G.Adj u a := by change a ∈ G.neighborSet u; rw [hN]; exact Or.inl rfl
    have hub : G.Adj u b := by change b ∈ G.neighborSet u; rw [hN]; exact Or.inr rfl
    have hNu : ∀ z, G.Adj u z → z=a ∨ z=b :=
      fun z hz ↦ (show z ∈ ({a,b} : Set (Fin n)) from hN ▸ hz)
    rcases one_neighbor_has_no_cross_edge hsmall hG hfail hu hua hub hab with ha|hb
    · exact two_outside_tip_region_of_clean_neighbor hsmall hG hfail hu hua hub hNu ha
    · exact two_outside_tip_region_of_clean_neighbor hsmall hG hfail hu hub hua
        (fun z hz ↦ (hNu z hz).symm) hb
  · have hR : tipRegion G=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨u,hu,_⟩
      exact hex ⟨u,hu⟩
    rw [hR,Set.compl_empty,Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_fin]
    have hn := LowDegreeAdjacency.failure_order_ge_five hG hfail
    omega

lemma degree_two_card_bound_strict {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) :
    3*{u | Nat.card (G.neighborSet u)=2}.ncard+2 ≤ n := by
  have hc := (tipRegion G).ncard_add_ncard_compl
  have htwo := two_outside_tip_region hsmall hG hfail
  rw [tipRegion_card hsmall hG hfail,Nat.card_eq_fintype_card,Fintype.card_fin] at hc
  omega

end Erdos583DegreeTwoSeparationDevelopment
