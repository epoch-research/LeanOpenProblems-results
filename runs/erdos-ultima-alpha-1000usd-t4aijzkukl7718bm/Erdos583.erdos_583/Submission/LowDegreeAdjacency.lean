import Submission.Work

/-! Low-degree adjacency restrictions in a smallest path-decomposition failure. -/
open SimpleGraph Erdos583Work
namespace Erdos583LowDegreeAdjacencyDevelopment
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

/-- Order minimality also applies to graphs with connected support, including
empty support. The budget is measured on the support, not the ambient type. -/
lemma smaller_orders_on_support {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : SupportConnected G)
    (hsize : G.support.ncard < n) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(G.support.ncard : ℚ)/2⌉₊ := by
  classical
  by_cases hn : G.support.Nonempty
  · obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G G.support hsize (hG.induce_support hn)
    obtain ⟨E,hE,hEc⟩ := hD.lift_induce_support G
    exact ⟨E,hE,hEc.trans hDc⟩
  · have he : G=⊥ := by
      apply bot_unique
      intro x y hxy
      exact (hn ⟨x,G.mem_support.mpr ⟨y,hxy⟩⟩).elim
    subst G
    exact ⟨∅,by simp [GoodDecomposition,IsDecomposition,Set.PairwiseDisjoint],by simp⟩

lemma gallai_of_two_vertex_support_reduction {n : ℕ} (hsmall : SmallerOrders n)
    (G H : SimpleGraph (Fin n)) (hH : SupportConnected H) (hc : H.support.ncard+2 ≤ n)
    (hlift : ∀ D : Finset H.Subgraph, GoodDecomposition H D →
      ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  obtain ⟨D,hD,hDc⟩ := smaller_orders_on_support hsmall H hH (by omega)
  obtain ⟨E,hE,hEc⟩ := hlift D hD
  rw [ceil_half] at hDc
  exact ⟨E,hE,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma failure_order_ge_five {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) : 5 ≤ n := by
  classical
  by_contra hn
  apply hfail
  apply subcubic_erdos_583 G hG
  intro v
  have hv := G.degree_lt_card_verts v
  simp only [Fintype.card_fin] at hv
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  omega

/-- The generic triangle reduction decreases support by two and costs at
most one path, so it applies in both order parities. -/
lemma no_triangle_degree_two_three {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {x u v a : Fin n}
    (hxu : G.Adj x u) (hxv : G.Adj x v) (huv : G.Adj u v) (hua : G.Adj u a)
    (hax : a ≠ x) (hav : a ≠ v)
    (hnx : ∀ z, G.Adj x z → z=u ∨ z=v)
    (hnu : ∀ z, G.Adj u z → z=x ∨ z=v ∨ z=a) : False := by
  obtain ⟨H,hH,hc,hlift⟩ := reduce_triangle_degree_two_three G
    (fun x _ y _ ↦ hG.preconnected x y) hxu hxv huv hua hax hav hnx hnu
  have hcG : G.support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using G.support.ncard_le_card
  exact hfail (gallai_of_two_vertex_support_reduction hsmall G H hH (by omega) hlift)

lemma neighbor_two_eq {V : Type*} [Fintype V] {G : SimpleGraph V} {u a b : V}
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b) (hu : Nat.card (G.neighborSet u)=2) :
    G.neighborSet u={a,b} := by
  have hs : ({a,b} : Set V) ⊆ G.neighborSet u := by
    rintro x (rfl|rfl) <;> assumption
  have hc : (G.neighborSet u).ncard=2 := by simpa only [Nat.card_coe_set_eq] using hu
  exact (Set.eq_of_subset_of_ncard_le hs (by rw [Set.ncard_pair hab]; omega)).symm

/-- Adjacent degree-two vertices would form a pendant triangle. Its odd
side order and even boundary degree contradict nontrivial cut parity. -/
lemma degree_two_not_adjacent_degree_two {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {x u : Fin n} (hxu : G.Adj x u)
    (hx : Nat.card (G.neighborSet x)=2) (hu : Nat.card (G.neighborSet u)=2) : False := by
  classical
  obtain ⟨_,a,b,hab,hN,habG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hx
  have huab : u=a ∨ u=b := (show u ∈ ({a,b} : Set (Fin n)) from hN ▸ hxu)
  have hex : ∃ v, G.Adj x v ∧ G.Adj u v ∧ u ≠ v ∧ G.neighborSet x={u,v} := by
    rcases huab with h|h
    · subst u
      exact ⟨b,by change b ∈ G.neighborSet x; rw [hN]; exact Or.inr rfl,habG,hab,hN⟩
    · subst u
      exact ⟨a,by change a ∈ G.neighborSet x; rw [hN]; exact Or.inl rfl,habG.symm,hab.symm,by rw [hN,Set.pair_comm]⟩
  obtain ⟨v,hxv,huv,huvne,hNx⟩ := hex
  have hNu := neighbor_two_eq hxu.symm huv hxv.ne hu
  let S : Set (Fin n) := {v,x,u}
  have hvS : v ∈ S := Or.inl rfl
  have hsize : S.ncard=3 := by simp [S,Set.ncard_insert_of_notMem,hxv.ne.symm,huv.ne.symm,hxu.ne]
  have hn := failure_order_ge_five hG hfail
  have hcsize : 2 ≤ Sᶜ.ncard := by
    rw [Set.ncard_compl,hsize,Nat.card_eq_fintype_card,Fintype.card_fin]
    omega
  have hcross : ∀ z ∈ S, ∀ w ∉ S, G.Adj z w → z=v := by
    intro z hz w hw hzw
    rcases hz with hz|hz|hz
    · exact hz
    · have hz' : z=x := hz
      subst z
      have hm : w=u ∨ w=v := (show w ∈ ({u,v} : Set (Fin n)) from hNx ▸ hzw)
      exact (hw (hm.elim (fun he ↦ Or.inr (Or.inr he)) Or.inl)).elim
    · have hz' : z=u := hz
      subst z
      have hm : w=x ∨ w=v := (show w ∈ ({x,v} : Set (Fin n)) from hNu ▸ hzw)
      exact (hw (hm.elim (fun he ↦ Or.inr (Or.inl he)) Or.inl)).elim
  have hpar := CutVertexParity.nontrivial_cut_side_parity hsmall hG hfail S v hvS hcross (by omega) hcsize
  have hcard : Nat.card ((G.induce S).neighborSet ⟨v,hvS⟩)=2 := by
    rw [CutVertexParity.induced_neighbor_card]
    have he : G.neighborSet v ∩ S={x,u} := by
      ext z
      constructor
      · rintro ⟨hz,hzS⟩
        rcases hzS with hzv|hzx|hzu
        · exact (hz.ne hzv.symm).elim
        · exact Or.inl hzx
        · exact Or.inr hzu
      · rintro (rfl|rfl)
        · exact ⟨hxv.symm,Or.inr (Or.inl rfl)⟩
        · exact ⟨huv.symm,Or.inr (Or.inr rfl)⟩
    rw [he,Set.ncard_pair hxu.ne]
  rw [hcard,hsize] at hpar
  norm_num at hpar

lemma degree_two_not_adjacent_degree_three {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {x u : Fin n} (hxu : G.Adj x u)
    (hx : Nat.card (G.neighborSet x)=2) (hu : Nat.card (G.neighborSet u)=3) : False := by
  obtain ⟨_,a,b,hab,hN,habG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hx
  have huab : u=a ∨ u=b := (show u ∈ ({a,b} : Set (Fin n)) from hN ▸ hxu)
  have hex : ∃ v, G.Adj x v ∧ G.Adj u v ∧ G.neighborSet x={u,v} := by
    rcases huab with h|h
    · subst u
      exact ⟨b,by change b ∈ G.neighborSet x; rw [hN]; exact Or.inr rfl,habG,hN⟩
    · subst u
      exact ⟨a,by change a ∈ G.neighborSet x; rw [hN]; exact Or.inl rfl,habG.symm,by rw [hN,Set.pair_comm]⟩
  obtain ⟨v,hxv,huv,hNx⟩ := hex
  obtain ⟨a,b,ha,hb,hab,hax,hbx,hNu⟩ := DegreeThreeReduction.degree_three_other_neighbors hxu.symm hu
  have hvab : v=a ∨ v=b := (hNu v huv).resolve_left hxv.ne.symm
  have hnx : ∀ z, G.Adj x z → z=u ∨ z=v := fun z hz ↦ (show z ∈ ({u,v} : Set (Fin n)) from hNx ▸ hz)
  rcases hvab with hva|hvb
  · subst a
    exact no_triangle_degree_two_three hsmall hG hfail hxu hxv huv hb hbx hab.symm hnx hNu
  · subst b
    apply no_triangle_degree_two_three hsmall hG hfail hxu hxv huv ha hax hab hnx
    intro z hz
    rcases hNu z hz with hh|hh|hh
    · exact Or.inl hh
    · exact Or.inr (Or.inr hh)
    · exact Or.inr (Or.inl hh)

/-- Every neighbor of a degree-two vertex in a smallest failure has degree
at least four. In particular, degree-two vertices are independent. -/
lemma degree_two_neighbors_ge_four {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {x u : Fin n} (hxu : G.Adj x u) (hx : Nat.card (G.neighborSet x)=2) :
    4 ≤ Nat.card (G.neighborSet u) := by
  have h2 := degree_two_not_adjacent_degree_two hsmall hG hfail hxu hx
  have h3 := degree_two_not_adjacent_degree_three hsmall hG hfail hxu hx
  obtain ⟨_,a,b,hab,hN,habG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hx
  have huab : u=a ∨ u=b := (show u ∈ ({a,b} : Set (Fin n)) from hN ▸ hxu)
  have hdeg : 2 ≤ Nat.card (G.neighborSet u) := by
    rw [Nat.card_coe_set_eq]
    rcases huab with h|h
    · subst u
      have hxb : G.Adj x b := by change b ∈ G.neighborSet x; rw [hN]; exact Or.inr rfl
      have hc := Set.ncard_mono (show ({x,b} : Set (Fin n)) ⊆ G.neighborSet a by
        rintro z (rfl|rfl)
        · exact hxu.symm
        · exact habG)
      rw [Set.ncard_pair hxb.ne] at hc
      exact hc
    · subst u
      have hxa : G.Adj x a := by change a ∈ G.neighborSet x; rw [hN]; exact Or.inl rfl
      have hc := Set.ncard_mono (show ({x,a} : Set (Fin n)) ⊆ G.neighborSet b by
        rintro z (rfl|rfl)
        · exact hxu.symm
        · exact habG.symm)
      rw [Set.ncard_pair hxa.ne] at hc
      exact hc
  by_contra hn
  have he : Nat.card (G.neighborSet u)=2 ∨ Nat.card (G.neighborSet u)=3 := by omega
  exact he.elim h2 h3

/-- If the actual failing graph has independent even-degree vertices, the
neighbors of its degree-two vertices have degree at least five. -/
lemma degree_two_neighbors_ge_five_of_even_independent {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hind : ∀ {a b}, Even (Nat.card (G.neighborSet a)) →
      Even (Nat.card (G.neighborSet b)) → ¬G.Adj a b)
    {x u : Fin n} (hxu : G.Adj x u) (hx : Nat.card (G.neighborSet x)=2) :
    5 ≤ Nat.card (G.neighborSet u) := by
  have h4 := degree_two_neighbors_ge_four hsmall hG hfail hxu hx
  have ho : Odd (Nat.card (G.neighborSet u)) := Nat.not_even_iff_odd.mp (fun he ↦
    hind (by rw [hx]; decide) he hxu)
  obtain ⟨k,hk⟩ := ho
  omega

lemma cubic_even_neighbor_ge_four {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r x : Fin n} (hrx : G.Adj r x) (hr : Nat.card (G.neighborSet r)=3)
    (hx : Even (Nat.card (G.neighborSet x))) : 4 ≤ Nat.card (G.neighborSet x) := by
  have hpos : 0 < Nat.card (G.neighborSet x) := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨r,hrx.symm⟩
  have hne : Nat.card (G.neighborSet x) ≠ 2 := by
    intro he
    have hh := degree_two_neighbors_ge_four hsmall hG hfail hrx.symm he
    omega
  obtain ⟨k,hk⟩ := hx
  omega

/-- A cubic rooted defect in a smallest failure exposes two even vertices
of degree at least four, rather than degree-two subdivision vertices. This
is only a restriction; it does not repair the defect. -/
lemma cubic_root_two_large_zero_neighbors {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {k : ℕ} (T : QuotaTrails.TrailFamily G k) (r : Fin n)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : QuotaTrails.TrailFamily G k, U.score ≤ T.score)
    (hroot : QuotaRooted.HasRoot T r) (hr : Nat.card (G.neighborSet r)=3) :
    ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧ T.quota x=0 ∧ T.quota y=0 ∧
      4 ≤ Nat.card (G.neighborSet x) ∧ 4 ≤ Nat.card (G.neighborSet y) ∧
      ¬G.IsBridge s(r,x) ∧ ¬G.IsBridge s(r,y) := by
  obtain ⟨x,y,hxy,hrx,hry,hx,hy,hbx,hby⟩ :=
    NonbridgeCore.two_zero_nonbridge_neighbors T r hs hm hroot
  exact ⟨x,y,hxy,hrx,hry,hx,hy,
    cubic_even_neighbor_ge_four hsmall hG hfail hrx hr (QuotaParity.zero_quota_even T hx),
    cubic_even_neighbor_ge_four hsmall hG hfail hry hr (QuotaParity.zero_quota_even T hy),hbx,hby⟩

end Erdos583LowDegreeAdjacencyDevelopment
