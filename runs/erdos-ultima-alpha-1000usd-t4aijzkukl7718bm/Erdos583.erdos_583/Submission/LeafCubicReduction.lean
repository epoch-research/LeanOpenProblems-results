import Submission.Work

/-! Suppression of a cubic neighbor of a leaf.  The second removed vertex
pays for the restored leaf in either order parity. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
open Erdos583Work.LeafPairReduction
namespace Erdos583LeafCubicReductionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma leaf_cubic_nonedge_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v a b : Fin n} (huv : G.Adj u v) (ha : G.Adj v a) (hb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) (hnab : ¬G.Adj a b)
    (hu : ∀ x, G.Adj u x → x=v)
    (hv : ∀ x, G.Adj v x → x=u ∨ x=a ∨ x=b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let T : Set (Fin n) := {u,v}
  let H := puncture G T ⊔ edge a b
  have haT : a ∉ T := by simp [T,hau,ha.ne.symm]
  have hbT : b ∉ T := by simp [T,hbu,hb.ne.symm]
  have haS : a ∈ G.support := G.mem_support.mpr ⟨v,ha.symm⟩
  have hbS : b ∈ G.support := G.mem_support.mpr ⟨v,hb.symm⟩
  have habH : H.Adj a b := Or.inr ((edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)
  have hcon : SupportConnected H := SupportConnected.puncture_add_edge
    (fun x _ y _ ↦ hG.preconnected x y) T hab haT haS hbS (by
      intro t ht x hx htx
      rcases ht with ht|ht
      · subst t; exact (hx (Or.inr (hu x htx))).elim
      · have ht' : t=v := ht
        subst t
        rcases hv x htx with hx'|hx'|hx'
        · exact (hx (Or.inl hx')).elim
        · subst x; exact .rfl
        · subst x; exact habH.reachable)
  have hsub : H.support ⊆ G.support \ T := by
    intro x hx
    obtain ⟨hxS,hxT⟩ := support_puncture_add_edge_subset T haS hbS hx
    refine ⟨hxS,fun hxt ↦ hxT ⟨hxt,?_⟩⟩
    rintro (hxa|hxb)
    · subst x; exact haT hxt
    · have hxb' : x=b := hxb
      subst x; exact hbT hxt
  have hTS : T ⊆ G.support := by
    rintro x (hx|hx)
    · subst x; exact G.mem_support.mpr ⟨v,huv⟩
    · have hx' : x=v := hx
      subst x; exact G.mem_support.mpr ⟨u,huv.symm⟩
  have hcard : H.support.ncard+2 ≤ n := by
    have hc := support_card_bound_of_removed hTS hsub
    have hT : T.ncard=2 := Set.ncard_pair huv.ne
    have hcG : G.support.ncard ≤ n := by simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using G.support.ncard_le_card
    omega
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce H H.support (by omega)
    (hcon.induce_support ⟨a,H.mem_support.mpr ⟨b,habH⟩⟩)
  obtain ⟨E,hE,hEc⟩ := hD.lift_induce_support H
  let P : G.Walk a b := .cons ha.symm (.cons hb .nil)
  let Q : G.Walk v u := .cons huv.symm .nil
  have hp : P.IsPath := by simp [P,Walk.cons_isPath_iff,ha.ne.symm,hb.ne,hab]
  have hq : Q.IsPath := by simp [Q,huv.ne.symm]
  obtain ⟨F,hF,hFc⟩ := hE.puncture_expand_restore T hab (fun hh ↦ hnab hh.1)
    P hp Q hq (by
      intro x hx hxa hxb
      have hxv : x=v := by simpa [P,hxa,hxb] using hx
      exact Or.inr hxv) (by
      intro t ht x htx
      simp only [P,Q,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
      rcases ht with ht|ht
      · subst t; have hx := hu x htx; subst x; exact Or.inr Sym2.eq_swap
      · have ht' : t=v := ht
        subst t
        rcases hv x htx with hx|hx|hx
        · subst x; exact Or.inr rfl
        · subst x; exact Or.inl (Or.inl Sym2.eq_swap)
        · subst x; exact Or.inl (Or.inr rfl)) (by
      intro e he
      have he' : e=s(v,u) := by simpa [Q] using he
      exact ⟨u,Or.inl rfl,by rw [he']; simp⟩) (by
      simp [P,Q,huv.ne,ha.ne,hb.ne,hau.symm,hbu.symm])
  rw [ceil_half] at hDc
  exact ⟨F,hF,by simp only [Fintype.card_fin,ceil_half]; omega⟩

/-- A cubic neighbor of a leaf in a smallest failure lies on a triangle. -/
lemma leaf_cubic_triangle_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : G.Adj u v) (hu : ∀ x, G.Adj u x → x=v)
    (hd : Nat.card (G.neighborSet v)=3) :
    ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
      G.Adj a b ∧ ∀ x, G.Adj v x → x=u ∨ x=a ∨ x=b := by
  obtain ⟨a,b,ha,hb,hab,hau,hbu,hv⟩ := DegreeThreeReduction.degree_three_other_neighbors huv.symm hd
  refine ⟨a,b,ha,hb,hab,hau,hbu,?_,hv⟩
  by_contra hn
  exact hfail (leaf_cubic_nonedge_reduction hsmall hG huv ha hb hab hau hbu hn hu hv)

lemma leaf_cubic_no_other_bridge_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v w : Fin n} (huv : G.Adj u v) (hu : ∀ x, G.Adj u x → x=v)
    (hd : Nat.card (G.neighborSet v)=3) (hwu : w ≠ u) : ¬G.IsBridge s(v,w) := by
  intro hbr
  obtain ⟨a,b,ha,hb,_,_,_,hab,hv⟩ := leaf_cubic_triangle_of_failure hsmall hG hfail huv hu hd
  rcases hv w (isBridge_iff.mp hbr).1 with hw|hw|hw
  · exact hwu hw
  · subst w
    exact DegreeThreeReduction.edge_with_common_neighbor_not_bridge hb hab.symm hbr
  · subst w
    exact DegreeThreeReduction.edge_with_common_neighbor_not_bridge ha hab hbr

/-- When two leaves exist, both their neighbors have degree at least five. -/
lemma two_leaf_neighbors_degree_ge_five {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v a b : Fin n} (huv : u ≠ v) (ha : G.Adj u a) (hb : G.Adj v b)
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=b) :
    5 ≤ Nat.card (G.neighborSet a) ∧ 5 ≤ Nat.card (G.neighborSet b) := by
  have hh := leaf_neighbors_bridge_of_failure hsmall hG hfail huv ha hb hu hv
  have ho := BridgeParityReduction.bridge_endpoints_odd_of_failure hsmall hG hfail hh.2
  have hla := leaf_neighbor_not_leaf_of_failure hG hfail ha hu
  have hlb := leaf_neighbor_not_leaf_of_failure hG hfail hb hv
  have hdu : Nat.card (G.neighborSet u)=1 := by
    have he : G.neighborSet u={a} := by ext x; exact ⟨hu x,fun h ↦ h ▸ ha⟩
    rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]
  have hdv : Nat.card (G.neighborSet v)=1 := by
    have he : G.neighborSet v={b} := by ext x; exact ⟨hv x,fun h ↦ h ▸ hb⟩
    rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]
  have hbu : b ≠ u := fun he ↦ hlb (he ▸ hdu)
  have hav : a ≠ v := fun he ↦ hla (he ▸ hdv)
  have ha3 : Nat.card (G.neighborSet a) ≠ 3 := fun hd ↦
    leaf_cubic_no_other_bridge_of_failure hsmall hG hfail ha hu hd hbu hh.2
  have hb3 : Nat.card (G.neighborSet b) ≠ 3 := fun hd ↦
    leaf_cubic_no_other_bridge_of_failure hsmall hG hfail hb hv hd hav (by simpa only [Sym2.eq_swap] using hh.2)
  obtain ⟨i,hi⟩ := ho.1
  obtain ⟨j,hj⟩ := ho.2
  omega

end Erdos583LeafCubicReductionDevelopment
