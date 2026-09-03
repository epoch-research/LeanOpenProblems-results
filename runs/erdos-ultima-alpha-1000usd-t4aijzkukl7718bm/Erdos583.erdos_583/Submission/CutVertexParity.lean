import Submission.Work
import Submission.DoubleEndpointGlue

/-! Parity restrictions at vertex cuts of a smallest path-decomposition failure. -/
open SimpleGraph Erdos583Work
namespace Erdos583CutVertexParityDevelopment
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical Erdos583Work.CutVertexReduction
open Erdos583DoubleEndpointGlueDevelopment
open scoped Classical
set_option maxHeartbeats 1600000

lemma induced_neighbor_card {V : Type*} {G : SimpleGraph V} (S : Set V) (u : V) (hu : u ∈ S) :
    Nat.card ((G.induce S).neighborSet ⟨u,hu⟩) = (G.neighborSet u ∩ S).ncard := by
  let e : (G.induce S).neighborSet ⟨u,hu⟩ ≃ ↥(G.neighborSet u ∩ S) := {
    toFun x := ⟨x.val.val, x.property, x.val.property⟩
    invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  rw [←Nat.card_coe_set_eq]
  exact Nat.card_congr e

lemma single_boundary_neighbor_sum {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) (u : V) (hu : u ∈ S) :
    Nat.card ((G.induce S).neighborSet ⟨u,hu⟩) +
      Nat.card ((G.induce (insert u Sᶜ)).neighborSet ⟨u,Or.inl rfl⟩) =
      Nat.card (G.neighborSet u) := by
  rw [induced_neighbor_card,induced_neighbor_card,Nat.card_coe_set_eq]
  have he : G.neighborSet u ∩ insert u Sᶜ = G.neighborSet u \ S := by
    ext x
    constructor
    · rintro ⟨hx,rfl|hxS⟩
      · exact (G.loopless _ hx).elim
      · exact ⟨hx,hxS⟩
    · rintro ⟨hx,hxS⟩
      exact ⟨hx,Or.inr hxS⟩
  rw [he,Set.ncard_inter_add_ncard_diff_eq_ncard]

/-- Odd/even sides can be glued within the vertex budget if the odd side
has even boundary degree, or the even side has odd boundary degree. -/
lemma gallai_odd_even_sides {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (S T : Set (Fin n)) (u : Fin n)
    (huS : u ∈ S) (huT : u ∈ T) (hinter : S ∩ T ⊆ {u})
    (hcover : (within G S).edgeSet ∪ (within G T).edgeSet=G.edgeSet)
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (hS : 3 ≤ S.ncard) (hT : 3 ≤ T.ncard) (hsum : S.ncard+T.ncard=n+1)
    (hoS : Odd S.ncard) (heT : Even T.ncard)
    (hpar : Even (Nat.card ((G.induce S).neighborSet ⟨u,huS⟩)) ∨
      Odd (Nat.card ((G.induce T).neighborSet ⟨u,huT⟩))) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  have hcardS : Fintype.card S=S.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hcardT : Fintype.card T=T.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨D,a,p,hD,hp,hm,hDc⟩ := smaller_order_marked hsmall (G.induce S) hconnS ⟨u,huS⟩
    (by rw [hcardS]; omega)
  obtain ⟨E,hE,hEc⟩ := hsmall.on_induce G T (by omega) hconnT
  have hg : ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+1 ≤ D.card+E.card := by
    rcases hpar with he|ho
    · letI : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hcardT]; omega)
      exact glue_induced_even_marked S T u huS huT hinter hcover D E hD hE he
        ⟨a,p,hp,hm⟩ (hconnT.preconnected.support_eq_univ.symm ▸ Set.mem_univ _)
    · have ho' : Odd ((G.induce T).degree ⟨u,huT⟩) := by
        simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using ho
      have hpos := ((hE.odd_endpointMultiplicity_iff ⟨u,huT⟩).mpr ho').pos
      obtain ⟨b,q,hq,hqm⟩ := MarkedBudgets.marked_of_positive_endpoint hE hpos
      exact glue_induced_sides S T u huS huT hinter hcover D E hD hE p q hp hq hm hqm
  obtain ⟨F,hF,hFc⟩ := hg
  obtain ⟨a,ha⟩ := hoS
  obtain ⟨b,hb⟩ := heT
  rw [hcardS,ceil_half] at hDc
  rw [ceil_half] at hEc
  exact ⟨F,hF,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma failure_odd_even_side_parity {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S T : Set (Fin n)) (u : Fin n) (huS : u ∈ S) (huT : u ∈ T)
    (hinter : S ∩ T ⊆ {u})
    (hcover : (within G S).edgeSet ∪ (within G T).edgeSet=G.edgeSet)
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (hS : 3 ≤ S.ncard) (hT : 3 ≤ T.ncard) (hsum : S.ncard+T.ncard=n+1)
    (hoS : Odd S.ncard) (heT : Even T.ncard) :
    Odd (Nat.card ((G.induce S).neighborSet ⟨u,huS⟩)) ∧
      Even (Nat.card ((G.induce T).neighborSet ⟨u,huT⟩)) := by
  have hn : ¬(Even (Nat.card ((G.induce S).neighborSet ⟨u,huS⟩)) ∨
      Odd (Nat.card ((G.induce T).neighborSet ⟨u,huT⟩))) := by
    intro hh
    exact hfail (gallai_odd_even_sides hsmall S T u huS huT hinter hcover hconnS hconnT hS hT hsum hoS heT hh)
  exact ⟨Nat.not_even_iff_odd.mp (not_or.mp hn).1,Nat.not_odd_iff_even.mp (not_or.mp hn).2⟩

/-- When both sides have at least three vertices, every boundary vertex of
a smallest failure has odd ambient degree. -/
lemma nontrivial_cut_boundary_odd {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) (u : Fin n) (hu : u ∈ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u)
    (hS : 3 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) : Odd (Nat.card (G.neighborSet u)) := by
  classical
  by_cases hn : Odd n
  · exact (hfail (single_boundary_budget hsmall hn hG S u hu hcross (by omega) (by omega))).elim
  have hen : Even n := Nat.not_odd_iff_even.mp hn
  let T : Set (Fin n) := insert u Sᶜ
  have huT : u ∈ T := Or.inl rfl
  have hinter : S ∩ T ⊆ {u} := by
    rintro x ⟨hx,rfl|hxc⟩
    · rfl
    · exact (hxc hx).elim
  have hconnS := single_boundary_connected hG S u hu hcross
  have hconnT := single_boundary_connected hG T u huT (opposite_single_boundary S u hcross)
  have hcover := single_boundary_cover S u hcross
  have hcT : T.ncard=Sᶜ.ncard+1 := Set.ncard_insert_of_notMem (not_not.mpr hu)
  have hsum : S.ncard+T.ncard=n+1 := by
    have hh : S.ncard+Sᶜ.ncard=n := by simpa using S.ncard_add_ncard_compl
    omega
  have hdeg := single_boundary_neighbor_sum (G := G) S u hu
  change Nat.card ((G.induce S).neighborSet ⟨u,hu⟩) +
    Nat.card ((G.induce T).neighborSet ⟨u,huT⟩) = Nat.card (G.neighborSet u) at hdeg
  by_cases hoS : Odd S.ncard
  · have heT : Even T.ncard := by
      obtain ⟨k,hk⟩ := hen
      obtain ⟨a,ha⟩ := hoS
      exact Nat.even_iff.mpr (by omega)
    obtain ⟨hs,ht⟩ := failure_odd_even_side_parity hsmall hfail S T u hu huT hinter hcover
      hconnS hconnT hS (by omega) hsum hoS heT
    exact hdeg ▸ hs.add_even ht
  · have heS : Even S.ncard := Nat.not_odd_iff_even.mp hoS
    have hoT : Odd T.ncard := by
      obtain ⟨k,hk⟩ := hen
      obtain ⟨a,ha⟩ := heS
      exact Nat.odd_iff.mpr (by omega)
    obtain ⟨ht,hs⟩ := failure_odd_even_side_parity hsmall hfail T S u huT hu
      (by simpa only [Set.inter_comm] using hinter) (by simpa only [Set.union_comm] using hcover)
      hconnT hconnS (by omega) hS (by omega) hoT heS
    exact hdeg ▸ hs.add_odd ht

/-- At a nontrivial vertex cut, internal boundary degree has the same
parity as the order of the induced side. -/
lemma nontrivial_cut_side_parity {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) (u : Fin n) (hu : u ∈ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u)
    (hS : 3 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) :
    Odd (Nat.card ((G.induce S).neighborSet ⟨u,hu⟩)) ↔ Odd S.ncard := by
  classical
  have hen : Even n := by
    apply Nat.not_odd_iff_even.mp
    intro hn
    exact hfail (single_boundary_budget hsmall hn hG S u hu hcross (by omega) (by omega))
  let T : Set (Fin n) := insert u Sᶜ
  have huT : u ∈ T := Or.inl rfl
  have hinter : S ∩ T ⊆ {u} := by
    rintro x ⟨hx,rfl|hxc⟩
    · rfl
    · exact (hxc hx).elim
  have hconnS := single_boundary_connected hG S u hu hcross
  have hconnT := single_boundary_connected hG T u huT (opposite_single_boundary S u hcross)
  have hcover := single_boundary_cover S u hcross
  have hcT : T.ncard=Sᶜ.ncard+1 := Set.ncard_insert_of_notMem (not_not.mpr hu)
  have hsum : S.ncard+T.ncard=n+1 := by
    have hh : S.ncard+Sᶜ.ncard=n := by simpa using S.ncard_add_ncard_compl
    omega
  by_cases hoS : Odd S.ncard
  · have heT : Even T.ncard := by
      obtain ⟨k,hk⟩ := hen
      obtain ⟨a,ha⟩ := hoS
      exact Nat.even_iff.mpr (by omega)
    have hs := (failure_odd_even_side_parity hsmall hfail S T u hu huT hinter hcover
      hconnS hconnT hS (by omega) hsum hoS heT).1
    exact ⟨fun _ ↦ hoS,fun _ ↦ hs⟩
  · have heS : Even S.ncard := Nat.not_odd_iff_even.mp hoS
    have hoT : Odd T.ncard := by
      obtain ⟨k,hk⟩ := hen
      obtain ⟨a,ha⟩ := heS
      exact Nat.odd_iff.mpr (by omega)
    have hs := (failure_odd_even_side_parity hsmall hfail T S u huT hu
      (by simpa only [Set.inter_comm] using hinter) (by simpa only [Set.union_comm] using hcover)
      hconnT hconnS (by omega) hS (by omega) hoT heS).2
    exact ⟨fun hh ↦ (Nat.not_even_iff_odd.mpr hh hs).elim,fun hh ↦ (hoS hh).elim⟩

lemma leaf_edge_bridge {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) (hleaf : ∀ x, G.Adj u x → x=v) : G.IsBridge s(u,v) := by
  apply isBridge_iff_adj_and_forall_walk_mem_edges.mpr
  refine ⟨h,?_⟩
  intro p
  cases p with
  | nil => exact (G.loopless _ h).elim
  | @cons _ x _ hx p =>
    have he : x=v := hleaf x hx
    simp only [Walk.edges_cons,List.mem_cons]
    exact Or.inl (by rw [he])

lemma two_vertex_side_bridge {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.Connected) (S : Set V) (u : V) (hu : u ∈ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u)
    (hS : S.ncard=2) : ∃ a, G.IsBridge s(u,a) := by
  classical
  have hcardS : Fintype.card S=S.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  letI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hconn := single_boundary_connected hG S u hu hcross
  obtain ⟨a,ha⟩ := (G.induce S).mem_support.mp (show (⟨u,hu⟩ : S) ∈ (G.induce S).support from
    hconn.preconnected.support_eq_univ.symm ▸ Set.mem_univ _)
  have h : G.Adj u a.val := ha
  have heS : S={u,a.val} := (Set.eq_of_subset_of_ncard_le (show ({u,a.val} : Set V) ⊆ S by
    rintro x (rfl|rfl)
    · exact hu
    · exact a.property) (by rw [Set.ncard_pair h.ne]; omega)).symm
  have hb := leaf_edge_bridge h.symm (by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [heS] at hxS
      rcases hxS with hxu|hxa
      · exact hxu
      · exact (hx.ne hxa.symm).elim
    · exact (h.ne (hcross a.val a.property x hxS hx).symm).elim)
  exact ⟨a.val,by simpa only [Sym2.eq_swap] using hb⟩

lemma cut_boundary_odd {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) (u : Fin n) (hu : u ∈ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u)
    (hS : 2 ≤ S.ncard) (hcS : 0 < Sᶜ.ncard) : Odd (Nat.card (G.neighborSet u)) := by
  by_cases hs : S.ncard=2
  · obtain ⟨a,ha⟩ := two_vertex_side_bridge hG S u hu hcross hs
    exact (BridgeParityReduction.bridge_endpoints_odd_of_failure hsmall hG hfail ha).1
  by_cases ht : Sᶜ.ncard=1
  · have hcT : (insert u Sᶜ).ncard=2 := by rw [Set.ncard_insert_of_notMem (not_not.mpr hu),ht]
    obtain ⟨a,ha⟩ := two_vertex_side_bridge hG (insert u Sᶜ) u (Or.inl rfl)
      (opposite_single_boundary S u hcross) hcT
    exact (BridgeParityReduction.bridge_endpoints_odd_of_failure hsmall hG hfail ha).1
  exact nontrivial_cut_boundary_odd hsmall hG hfail S u hu hcross (by omega) (by omega)

/-- Deleting an even-degree vertex from a smallest-order failure leaves a
connected graph. This applies in both order parities. -/
lemma delete_even_vertex_connected_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (u : Fin n) (heven : Even (Nat.card (G.neighborSet u))) :
    (G.induce ({u}ᶜ : Set (Fin n))).Connected := by
  classical
  by_contra hconn
  obtain ⟨v,w,hvw,_,_⟩ := EdgeDefect.failure_has_even_nonbridge G hfail
  letI : Nontrivial (Fin n) := ⟨⟨w,v,hvw.ne⟩⟩
  obtain ⟨a,ha⟩ := G.mem_support.mp (show u ∈ G.support from
    hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ u)
  obtain ⟨b,hb,hnon⟩ : ∃ b, G.Adj u b ∧ ¬(within G ({u}ᶜ : Set (Fin n))).Reachable a b := by
    by_contra! hh
    exact hconn (DegreeThreeReduction.delete_vertex_connected_of_neighbor_links hG ha hh)
  let S : Set (Fin n) := {x | x=u ∨ (within G ({u}ᶜ : Set (Fin n))).Reachable a x}
  have hu : u ∈ S := Or.inl rfl
  have haS : a ∈ S := Or.inr Reachable.rfl
  have hbS : b ∉ S := by
    rintro (hbu|hr)
    · exact hb.ne hbu.symm
    · exact hnon hr
  have hsize : 2 ≤ S.ncard := by
    have hh : ({u,a} : Set (Fin n)) ⊆ S := by rintro x (rfl|rfl) <;> assumption
    have hc := Set.ncard_mono hh
    rw [Set.ncard_pair ha.ne] at hc
    exact hc
  have hcsize : 0 < Sᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨b,hbS⟩
  have ho := cut_boundary_odd hsmall hG hfail S u hu (by
    intro x hx y hy hxy
    rcases hx with hxu|hr
    · exact hxu
    by_contra hxu
    have hyu : y ≠ u := fun he ↦ hy (Or.inl he)
    exact hy (Or.inr (hr.trans (show (within G ({u}ᶜ : Set (Fin n))).Adj x y from ⟨hxy,hxu,hyu⟩).reachable)))
    hsize hcsize
  exact Nat.not_even_iff_odd.mpr ho heven

end Erdos583CutVertexParityDevelopment
