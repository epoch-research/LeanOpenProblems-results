import Submission.DeleteTriangleLink

/-! In a smallest-order failure, every neighbor of a degree-two vertex has degree at least five. -/
namespace Erdos583DegreeTwoNeighborFiveDevelopment
open SimpleGraph Erdos583Work
open Erdos583DeleteTriangleLinkDevelopment Erdos583DegreeTwoFourTriangleDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_triangle_degree_two_four {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r x y : Fin n} (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=2) : False := by
  classical
  obtain ⟨a,b,hxa,hxb,hab,hra,hrb,hya,hyb,hNx⟩ :=
    DegreeFourReduction.degree_four_other_neighbors hrx.symm hxy hry.ne hdx
  have hNy : ∀ z, G.Adj y z → z=r ∨ z=x := by
    have he := LowDegreeAdjacency.neighbor_two_eq hry.symm hxy.symm hrx.ne hdy
    intro z hz
    exact (show z ∈ ({r,x} : Set (Fin n)) from he ▸ hz)
  have hconn := CutVertexParity.delete_even_vertex_connected_of_failure hsmall hG hfail x
    (by rw [hdx]; decide)
  let C : Set (Sym2 (Fin n)) := {s(r,x),s(x,y),s(r,y)}
  let F := G.deleteEdges C
  have hHle : puncture G ({x,y} : Set (Fin n)) ≤ F := puncture_pair_le_delete_triangle G r x y
  have hraH : (puncture G ({x,y} : Set (Fin n))).Reachable r a :=
    puncture_pair_reachable_of_leaf hconn hNy hrx.ne hry.ne hxa.ne.symm hya.symm
  have hraF : F.Reachable r a := hraH.mono hHle
  have hxaF : F.Adj x a := by
    apply deleteEdges_adj.mpr
    refine ⟨hxa,?_⟩
    simp [C,hrx.ne.symm,hxy.ne,hra.symm,hya.symm]
  have hxbF : F.Adj x b := by
    apply deleteEdges_adj.mpr
    refine ⟨hxb,?_⟩
    simp [C,hrx.ne.symm,hxy.ne,hrb.symm,hyb.symm]
  have hF : SupportConnected F := delete_triangle_connected_of_tip_link hG hNy (hraF.trans hxaF.symm.reachable)
  have hyF : y ∉ F.support := delete_triangle_tip_support hNy
  have hrF : r ∈ F.support := mem_support_of_reachable hra hraF
  have hdis : Disjoint C F.edgeSet := by
    rw [edgeSet_deleteEdges]
    exact Set.disjoint_left.mpr (fun _ he hh ↦ hh.2 he)
  have hcover : G.edgeSet=F.edgeSet ∪ C := by
    rw [edgeSet_deleteEdges]
    apply (Set.diff_union_of_subset _).symm
    rintro e (rfl|rfl|rfl)
    · exact hrx
    · exact hxy
    · exact hry
  have hNxF : ∀ z, F.Adj x z → z=a ∨ z=b := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNx z hz with rfl | rfl | h | h
    · exact (hnz (Or.inl Sym2.eq_swap)).elim
    · exact (hnz (Or.inr (Or.inl rfl))).elim
    · exact Or.inl h
    · exact Or.inr h
  exact failure_no_triangle_two_four_data hsmall hG hfail (deleteEdges_le C) hF hrx hxy hry
    hdis hcover hrF hyF hxaF hxbF hab hra.symm hrb.symm hya.symm hyb.symm hNxF

lemma degree_two_not_adjacent_degree_four {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {x y : Fin n} (hxy : G.Adj x y)
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=2) : False := by
  obtain ⟨_,a,b,hab,hN,habG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hdy
  have hxab : x=a ∨ x=b := (show x ∈ ({a,b} : Set (Fin n)) from hN ▸ hxy.symm)
  have hex : ∃ r, G.Adj r x ∧ G.Adj r y := by
    rcases hxab with hx | hx
    · subst x
      refine ⟨b,habG.symm,?_⟩
      have hh : G.Adj y b := by change b ∈ G.neighborSet y; rw [hN]; exact Or.inr rfl
      exact hh.symm
    · subst x
      refine ⟨a,habG,?_⟩
      have hh : G.Adj y a := by change a ∈ G.neighborSet y; rw [hN]; exact Or.inl rfl
      exact hh.symm
  obtain ⟨r,hrx,hry⟩ := hex
  exact failure_no_triangle_degree_two_four hsmall hG hfail hrx hxy hry hdx hdy

lemma degree_two_neighbors_ge_five {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {x y : Fin n} (hxy : G.Adj x y) (hdx : Nat.card (G.neighborSet x)=2) :
    5 ≤ Nat.card (G.neighborSet y) := by
  have hlo := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hxy hdx
  have hn : Nat.card (G.neighborSet y) ≠ 4 := fun hdy ↦
    degree_two_not_adjacent_degree_four hsmall hG hfail hxy.symm hdy hdx
  omega

end Erdos583DegreeTwoNeighborFiveDevelopment
