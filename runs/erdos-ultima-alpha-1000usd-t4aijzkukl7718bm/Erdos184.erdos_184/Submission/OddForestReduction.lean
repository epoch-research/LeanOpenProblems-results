import Submission.EdgeHullPotential

/-! A forest can correct degree parity to odd away from one chosen vertex.
This does not provide the path decomposition needed to close the terminal case. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.Vertex
set_option maxHeartbeats 200000
variable {V : Type*} [Fintype V]

lemma exists_forest_same_parity (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeFinset.card ≤ Fintype.card V ∧
      ∀ v : V, F.degree v % 2 = G.degree v % 2 := by
  obtain ⟨F,hFG,hacyc,hcard,heven⟩ := exists_even_complement_forest G
  refine ⟨F,hFG,hacyc,hcard,?_⟩
  intro v
  have hd := degree_sdiff_add G F hFG v
  have he := Nat.even_iff.mp (heven v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd he ⊢
  omega

lemma exists_parity_forest {G : SimpleGraph V} (hG : G.Preconnected)
    (S : Finset V) (hS : Even S.card) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeFinset.card ≤ Fintype.card V ∧
      ∀ v : V, F.degree v % 2 = if v ∈ S then 1 else 0 := by
  obtain ⟨R,hRG,hR⟩ := exists_parity_subgraph hG S hS
  obtain ⟨F,hFR,hacyc,hcard,hpar⟩ := exists_forest_same_parity R
  refine ⟨F,hFR.trans hRG,hacyc,hcard,?_⟩
  intro v
  have hf := hpar v
  have hr := hR v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hf hr ⊢
  exact hf.trans hr

/-- In a connected graph, deleting a forest makes every degree odd except
possibly that of a specified vertex. The correction uses fewer than n edges. -/
lemma exists_odd_complement_forest_except {G : SimpleGraph V}
    (hG : G.Preconnected) (r : V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeFinset.card < Fintype.card V ∧
      ∀ v : V, v ≠ r → Odd ((G \ F).degree v) := by
  let S : Finset V := Finset.univ.filter (fun v => Even (G.degree v))
  obtain ⟨R,hRG,hR⟩ := parity_subgraph_with_root hG r S
  obtain ⟨F,hFR,hacyc,_,hpar⟩ := exists_forest_same_parity R
  have hFG := hFR.trans hRG
  haveI : Nonempty V := ⟨r⟩
  refine ⟨F,hFG,hacyc,acyclic_card_edges_lt F hacyc,?_⟩
  intro v hvr
  have hr := hR v
  have hf := hpar v
  have hd := degree_sdiff_add G F hFG v
  have hmem : v ∈ S ↔ Even (G.degree v) := by simp [S]
  simp only [hvr,if_false,add_zero] at hr
  rw [Nat.odd_iff]
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hr hf hd hmem ⊢
  by_cases hv : v ∈ S
  · have he := Nat.even_iff.mp (hmem.mp hv)
    rw [if_pos hv] at hr
    omega
  · have he : ¬ Even (Nat.card (G.neighborSet v)) := fun he => hv (hmem.mpr he)
    rw [Nat.even_iff] at he
    rw [if_neg hv] at hr
    omega

lemma odd_at_exception_of_even_order {G : SimpleGraph V} (r : V)
    (hV : Even (Fintype.card V))
    (hodd : ∀ v : V, v ≠ r → Odd (G.degree v)) : Odd (G.degree r) := by
  by_contra hr
  have he := G.even_card_odd_degree_vertices
  have hset : (Finset.univ.filter (fun v : V => Odd (G.degree v))) = Finset.univ.erase r := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true]
    constructor
    · intro hv hvr
      subst v
      exact hr hv
    · exact hodd v
  rw [hset,Finset.card_erase_of_mem (Finset.mem_univ r),Finset.card_univ] at he
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  rw [Nat.even_iff] at hV he
  omega

/-- For a connected graph of positive even order, the parity correction can
make every remaining degree odd, while deleting fewer than n edges. -/
lemma exists_odd_complement_forest [Nonempty V] {G : SimpleGraph V}
    (hG : G.Preconnected) (hV : Even (Fintype.card V)) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeFinset.card < Fintype.card V ∧ ∀ v : V, Odd ((G \ F).degree v) := by
  obtain ⟨r⟩ := ‹Nonempty V›
  obtain ⟨F,hFG,hacyc,hcard,hodd⟩ := exists_odd_complement_forest_except hG r
  refine ⟨F,hFG,hacyc,hcard,?_⟩
  have hr := odd_at_exception_of_even_order (G := G \ F) r hV (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hodd)
  intro v
  by_cases hvr : v = r
  · subst v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr
  · exact hodd v hvr

end Erdos184Work.Vertex

#print axioms Erdos184Work.Vertex.exists_parity_forest
#print axioms Erdos184Work.Vertex.exists_odd_complement_forest_except

#print axioms Erdos184Work.Vertex.exists_odd_complement_forest
