import Submission.ThreeEvenNontriangle
import Submission.CriticalEvenParity

/-! The ceiling-half path bound for graphs with exactly five even vertices.
This does not assert the unrestricted Gallai conjecture. -/
namespace Erdos583FiveEvenBoundDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.ComponentDeficit Erdos583Work.TipParity Erdos583Work.BridgeGlue
open Erdos583ThreeEvenNontriangleDevelopment Erdos583CriticalEvenParityDevelopment
open Erdos583EvenEdgeRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma delete_even_ends_path_evenCount {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (hab : a ≠ b) (ha : Even (Nat.card (G.neighborSet a)))
    (hb : Even (Nat.card (G.neighborSet b))) :
    evenCount (G.deleteEdges P.toSubgraph.edgeSet)+2=evenCount G := by
  classical
  have hodd (x : V) (hx : x=a ∨ x=b) :
      Odd (Nat.card ((G.deleteEdges P.toSubgraph.edgeSet).neighborSet x)) := by
    have hs := ncard_neighbor_delete_subgraph_add P.toSubgraph x
    rw [path_neighbor_ncard_formula hp (Walk.not_nil_of_ne hab) x,if_pos hx] at hs
    have he : Even (Nat.card (G.neighborSet x)) := hx.elim (fun h ↦ h ▸ ha) (fun h ↦ h ▸ hb)
    simp only [Nat.card_coe_set_eq,Nat.even_iff,Nat.odd_iff] at he ⊢
    omega
  let S := {x | Even (Nat.card (G.neighborSet x))}
  have heq : {x | Even (Nat.card ((G.deleteEdges P.toSubgraph.edgeSet).neighborSet x))}=
      S \ {a,b} := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,S]
    by_cases hxa : x=a
    · subst x
      simp only [Nat.not_even_iff_odd.mpr (hodd a (Or.inl rfl)),true_or,not_true_eq_false,and_false]
    by_cases hxb : x=b
    · subst x
      simp only [Nat.not_even_iff_odd.mpr (hodd b (Or.inr rfl)),or_true,not_true_eq_false,and_false]
    · simp only [hxa,hxb,or_self,not_false_eq_true,and_true]
      exact delete_path_degree_parity P hp hxa hxb
  have hsub : ({a,b} : Set V) ⊆ S := by
    rintro x (rfl|rfl) <;> assumption
  have hc := Set.ncard_diff_add_ncard_of_subset hsub
  rw [Set.ncard_pair hab] at hc
  simpa only [evenCount,heq,S] using hc

lemma five_even_bound_of_path {a b c d : V} (he : evenCount G=5)
    (P : G.Walk a b) (hp : P.IsPath) (hab : a ≠ b)
    (ha : Even (Nat.card (G.neighborSet a))) (hb : Even (Nat.card (G.neighborSet b)))
    (hc : Even (Nat.card (G.neighborSet c))) (hd : Even (Nat.card (G.neighborSet d)))
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d)
    (hmissing : ¬(G.deleteEdges P.toSubgraph.edgeSet).Adj c d) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  have hcount : evenCount (G.deleteEdges P.toSubgraph.edgeSet)=3 := by
    have hh := delete_even_ends_path_evenCount P hp hab ha hb
    omega
  obtain ⟨D,hD,hDc⟩ := sharp_three_even_not_clique (G.deleteEdges P.toSubgraph.edgeSet)
    hcount hcd ((delete_path_degree_parity P hp hca hcb).mpr hc)
    ((delete_path_degree_parity P hp hda hdb).mpr hd) hmissing
  obtain ⟨E,hE,hEc⟩ := restore_path_subgraph (show IsPathSubgraph P.toSubgraph from ⟨a,b,P,hp,rfl⟩) hD
  exact ⟨E,hE,by rw [ceil_half]; omega⟩

lemma five_even_nonclique (he : evenCount G=5) {c d : V} (hcd : c ≠ d)
    (hc : Even (Nat.card (G.neighborSet c))) (hd : Even (Nat.card (G.neighborSet d)))
    (hmissing : ¬G.Adj c d) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  let S := {x | Even (Nat.card (G.neighborSet x))} \ {c,d}
  have hcard : S.ncard=3 := by
    have hsub : ({c,d} : Set V) ⊆ {x | Even (Nat.card (G.neighborSet x))} := by
      rintro x (rfl|rfl) <;> assumption
    have hh := Set.ncard_diff_add_ncard_of_subset hsub
    rw [Set.ncard_pair hcd] at hh
    change S.ncard+2=evenCount G at hh
    omega
  obtain ⟨a,b,ha,hb,hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite S)).mp (by omega : 1 < S.ncard)
  have hac : a ≠ c := fun h ↦ ha.2 (Or.inl h)
  have had : a ≠ d := fun h ↦ ha.2 (Or.inr h)
  have hbc : b ≠ c := fun h ↦ hb.2 (Or.inl h)
  have hbd : b ≠ d := fun h ↦ hb.2 (Or.inr h)
  by_cases hadj : G.Adj a b
  · let P : G.Walk a b := .cons hadj .nil
    apply five_even_bound_of_path he P (by simp [P,hab]) hab ha.1 hb.1 hc hd
      hac.symm hbc.symm had.symm hbd.symm hcd
    exact fun hh ↦ hmissing hh.1
  · let J := G ⊔ edge a b
    have hcount : evenCount J=3 := by
      have hh := evenCount_add_even_edge hab hadj ha.1 hb.1
      change evenCount J+2=evenCount G at hh
      omega
    have hce : Even (Nat.card (J.neighborSet c)) := by
      rwa [sup_edge_neighbor_card_of_ne hac.symm hbc.symm]
    have hde : Even (Nat.card (J.neighborSet d)) := by
      rwa [sup_edge_neighbor_card_of_ne had.symm hbd.symm]
    have hm : ¬J.Adj c d := by
      simp only [J,sup_adj,edge_adj,hac.symm,hbc.symm,false_and,or_false]
      exact hmissing
    obtain ⟨D,hD,hDc⟩ := sharp_three_even_not_clique J hcount hcd hce hde hm
    have hJab : J.Adj a b := Or.inr (by simp [edge_adj,hab])
    obtain ⟨E,hE,hEc⟩ := delete_edge_decomposition hD ⟨s(a,b),hJab⟩
    have hJG : J.deleteEdges {s(a,b)}=G := by
      ext x y
      simp only [deleteEdges_adj,J,sup_adj,edge_adj,Set.mem_singleton_iff,Sym2.eq_iff]
      constructor
      · rintro ⟨h,hn⟩
        rcases h with h|h
        · exact h
        · exact (hn h.1).elim
      · intro h
        refine ⟨Or.inl h,?_⟩
        rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
        · exact hadj h
        · exact hadj h.symm
    have hex : ∃ E : Finset (J.deleteEdges {s(a,b)}).Subgraph,
        GoodDecomposition (J.deleteEdges {s(a,b)}) E ∧
        E.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ :=
      ⟨E,hE,by rw [ceil_half]; omega⟩
    rwa [hJG] at hex

lemma five_even_clique (he : evenCount G=5)
    (hclique : ∀ a b, Even (Nat.card (G.neighborSet a)) →
      Even (Nat.card (G.neighborSet b)) → a ≠ b → G.Adj a b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hac,had,hbc,hbd,hcd⟩ :=
    (Set.three_lt_ncard_iff (Set.toFinite {x | Even (Nat.card (G.neighborSet x))})).mp
      (by change 3 < evenCount G; omega)
  let P : G.Walk a d := .cons (hclique a b ha hb hab)
    (.cons (hclique b c hb hc hbc) (.cons (hclique c d hc hd hcd) .nil))
  have hp : P.IsPath := by
    simp [Walk.isPath_def,P,hab,hac,had,hbc,hbd,hcd]
  apply five_even_bound_of_path he P hp had ha hd hb hc hab.symm hbd hac.symm hcd hbc
  intro hh
  exact (deleteEdges_adj.mp hh).2
    (P.mem_edges_toSubgraph.mpr (show s(b,c) ∈ P.edges by simp [P]))

lemma five_even_path_bound (he : evenCount G=5) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  by_cases hc : ∀ a b, Even (Nat.card (G.neighborSet a)) →
      Even (Nat.card (G.neighborSet b)) → a ≠ b → G.Adj a b
  · exact five_even_clique he hc
  · push_neg at hc
    obtain ⟨a,b,ha,hb,hab,hm⟩ := hc
    exact five_even_nonclique he hab ha hb hm

lemma odd_order_at_most_five_even (ho : Odd (Fintype.card V)) (he : evenCount G ≤ 5) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  by_cases h5 : evenCount G=5
  · exact five_even_path_bound h5
  · have hp := (odd_order_iff_evenCount_odd G).mp ho
    have h3 : evenCount G ≤ 3 := by rw [Nat.odd_iff] at hp; omega
    apply EndpointSelection.gallai_of_at_most_three_even G
    rw [evenCount_eq_filter] at h3
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using h3

end Erdos583FiveEvenBoundDevelopment
