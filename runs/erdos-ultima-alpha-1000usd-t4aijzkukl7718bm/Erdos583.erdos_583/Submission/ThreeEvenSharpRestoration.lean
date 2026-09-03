import Submission.EvenEdgeRestoration

/-! A sharp floor-half restoration result for three even vertices whose
induced graph is a nonempty forest. This does not cover three independent
even vertices or assert the general Gallai conjecture. -/
namespace Erdos583ThreeEvenSharpRestorationDevelopment
open SimpleGraph Erdos583Work Erdos583EvenEdgeRestorationDevelopment
open Erdos583Work.ComponentDeficit
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma sharp_three_even_forest_edge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hthree : evenCount G=3)
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic)
    {u v : V} (h : G.Adj v u)
    (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  classical
  have hcount : evenCount (G.deleteEdges {s(v,u)})=1 := by
    have hh := even_count_delete_edge h hu hv
    rw [←evenCount_eq_filter,←evenCount_eq_filter,hthree] at hh
    omega
  obtain ⟨D,hD,hDc⟩ := sharp_one_even_partition (G.deleteEdges {s(v,u)}) hcount
  obtain ⟨E,hE,hEc⟩ := EdgeCritical.restore_even_even_edge_of_even_forest
    h hu hv hf D hD (le_refl D.card)
  exact ⟨E,hE,by omega⟩

lemma triple_even_set_of_card_three {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hthree : evenCount G=3) {a u v : V} (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v)
    (ha : Even (Nat.card (G.neighborSet a)))
    (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) :
    {x | Even (Nat.card (G.neighborSet x))}=({a,u,v} : Set V) := by
  have hsub : ({a,u,v} : Set V) ⊆ {x | Even (Nat.card (G.neighborSet x))} := by
    rintro x (rfl|rfl|rfl) <;> assumption
  apply (Set.eq_of_subset_of_ncard_le hsub ?_).symm
  change evenCount G ≤ _
  simp [hthree,Set.ncard_insert_of_notMem,hau,hav,huv]

lemma triple_induce_acyclic_of_nonedge {V : Type*} (G : SimpleGraph V)
    (a u v : V) (hnot : ¬G.Adj a u) :
    (G.induce ({a,u,v} : Set V)).IsAcyclic := by
  apply acyclic_of_edges_incident (G := G.induce ({a,u,v} : Set V)) ⟨v,by simp⟩
  intro x y hxy
  by_cases hxv : x.val=v
  · exact Or.inl (Subtype.ext hxv)
  by_cases hyv : y.val=v
  · exact Or.inr (Subtype.ext hyv)
  have hx : x.val=a ∨ x.val=u := by
    have hh := x.property
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
    tauto
  have hy : y.val=a ∨ y.val=u := by
    have hh := y.property
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
    tauto
  change G.Adj x.val y.val at hxy
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · rw [hx,hy] at hxy; exact (G.irrefl hxy).elim
  · rw [hx,hy] at hxy; exact (hnot hxy).elim
  · rw [hx,hy] at hxy; exact (hnot hxy.symm).elim
  · rw [hx,hy] at hxy; exact (G.irrefl hxy).elim

/-- Three even vertices, an even-even edge, and a missing edge among the
three give the floor-half bound. No connectedness hypothesis is needed. -/
lemma sharp_three_even_edge_nonedge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hthree : evenCount G=3) (a u v : V) (hau : a ≠ u) (hav : a ≠ v)
    (h : G.Adj v u)
    (ha : Even (Nat.card (G.neighborSet a)))
    (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) (hnot : ¬G.Adj a u) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  apply sharp_three_even_forest_edge G hthree (u := u) (v := v) ?_ h hu hv
  rw [triple_even_set_of_card_three G hthree hau hav h.ne.symm ha hu hv]
  exact triple_induce_acyclic_of_nonedge G a u v hnot

end Erdos583ThreeEvenSharpRestorationDevelopment
