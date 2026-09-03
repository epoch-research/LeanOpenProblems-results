import Submission.EdgeHullExtremal

/-! Neighborhood compression preserves edge count and increases the degree-square
potential unless adjacent neighborhoods are nested. The needed decomposition-
number compression hypothesis is not established in this file. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.Compression
set_option maxHeartbeats 200000
variable {V : Type*} [Fintype V]

lemma sum_exchange_two (f g : V → ℕ) {u v : V} (huv : u ≠ v)
    (haway : ∀ w : V, w ≠ u → w ≠ v → f w = g w) :
    (∑ w : V, f w) + g u + g v = (∑ w : V, g w) + f u + f v := by
  have hfu := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ u)
  have hgu := Finset.sum_erase_add (s := Finset.univ) g (Finset.mem_univ u)
  have hv : v ∈ (Finset.univ : Finset V).erase u := by simp [Ne.symm huv]
  have hfv := Finset.sum_erase_add _ f hv
  have hgv := Finset.sum_erase_add _ g hv
  have hr : ∑ w ∈ ((Finset.univ : Finset V).erase u).erase v, f w =
      ∑ w ∈ ((Finset.univ : Finset V).erase u).erase v, g w := by
    apply Finset.sum_congr rfl
    intro w hw
    exact haway w (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1 (Finset.mem_erase.mp hw).1
  omega

lemma transfer_edge_card (G : SimpleGraph V) (u v : V) :
    (transfer G u v).edgeFinset.card = G.edgeFinset.card := by
  by_cases huv : u = v
  · subst v
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,transfer_self]
  have hl := transfer_degree_left (G := G) huv
  have hr := transfer_degree_right (G := G) huv
  have hs := sum_exchange_two (fun w => Nat.card ((transfer G u v).neighborSet w))
    (fun w => Nat.card (G.neighborSet w)) huv (by
      intro w hwu hwv
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using transfer_degree_other (G := G) hwu hwv)
  dsimp only at hs
  have hg := G.sum_degrees_eq_twice_card_edges
  have ht := (transfer G u v).sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree,SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hl hr hg ht ⊢
  omega

noncomputable def degreePotential (G : SimpleGraph V) : ℕ :=
  ∑ w : V, (Nat.card (G.neighborSet w)) ^ 2

lemma transfer_potential_lt (G : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (hdeg : Nat.card (G.neighborSet v) ≤ Nat.card (G.neighborSet u))
    (hpriv : (privateNeighbors G u v).Nonempty) :
    degreePotential G < degreePotential (transfer G u v) := by
  have hl := transfer_degree_left (G := G) huv
  have hr := transfer_degree_right (G := G) huv
  have hp : 0 < (privateNeighbors G u v).card := Finset.card_pos.mpr hpriv
  have hs := sum_exchange_two (fun w => (Nat.card ((transfer G u v).neighborSet w)) ^ 2)
    (fun w => (Nat.card (G.neighborSet w)) ^ 2) huv (by
      intro w hwu hwv
      have h := transfer_degree_other (G := G) hwu hwv
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h
      exact congrArg (fun n : ℕ => n ^ 2) h)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hr
  change degreePotential (transfer G u v) + _ + _ = degreePotential G + _ + _ at hs
  have hm := Nat.mul_le_mul_left (privateNeighbors G u v).card hdeg
  have hp2 : 0 < (privateNeighbors G u v).card ^ 2 := pow_pos hp _
  nlinarith

/-- At every edge, the lower-degree endpoint has no private neighbor other
than the higher-degree endpoint itself. -/
def NestedAlongEdges (G : SimpleGraph V) : Prop :=
  ∀ u v : V, G.Adj u v → Nat.card (G.neighborSet v) ≤ Nat.card (G.neighborSet u) →
    ∀ w : V, w ≠ u → G.Adj v w → G.Adj u w

lemma exists_improving_transfer (G : SimpleGraph V) (hn : ¬ NestedAlongEdges G) :
    ∃ u v : V, G.Adj u v ∧ degreePotential G < degreePotential (transfer G u v) := by
  simp only [NestedAlongEdges,not_forall,Classical.not_imp] at hn
  obtain ⟨u,v,huv,hdeg,w,hwu,hvw,huw⟩ := hn
  exact ⟨u,v,huv,transfer_potential_lt G huv.ne hdeg
    ⟨w,mem_privateNeighbors.mpr ⟨hwu,hvw,huw⟩⟩⟩

/-- A connected graph with nested adjacent neighborhoods has a universal vertex. -/
lemma NestedAlongEdges.exists_universal {G : SimpleGraph V}
    (hG : NestedAlongEdges G) (hconn : G.Connected) :
    ∃ u : V, ∀ v : V, v ≠ u → G.Adj u v := by
  haveI : Nonempty V := hconn.nonempty
  obtain ⟨u,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (fun v => Nat.card (G.neighborSet v)) Finset.univ_nonempty
  have hstep : ∀ x y : V, (x = u ∨ G.Adj u x) → G.Adj x y → y = u ∨ G.Adj u y := by
    intro x y hx hxy
    rcases hx with rfl | hux
    · exact Or.inr hxy
    · by_cases hyu : y = u
      · exact Or.inl hyu
      · exact Or.inr (hG u x hux (hmax x (Finset.mem_univ x)) y hyu hxy)
  have hwalk : ∀ {x y : V}, G.Walk x y → (x = u ∨ G.Adj u x) → y = u ∨ G.Adj u y := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z hxy p ih => exact fun hx => ih (hstep x y hx hxy)
  refine ⟨u,?_⟩
  intro v hvu
  obtain ⟨p⟩ := hconn.preconnected u v
  rcases hwalk p (Or.inl rfl) with h | h
  · exact (hvu h).elim
  · exact h

end Erdos184Work.Compression

namespace Erdos184Work.EdgeHull
open Compression Critical
variable {V : Type*} [Fintype V]

/-- Only two substantive hypotheses remain in this route: compression of
minimal graphs along their own edges, and a bound for nested-neighborhood graphs. -/
lemma bound_of_compression_and_nested
    (k : ℕ)
    (hcompression : ∀ G : SimpleGraph V, Minimal G → ∀ u v : V, G.Adj u v →
      number G ≤ value (transfer G u v))
    (hterminal : ∀ G : SimpleGraph V, NestedAlongEdges G → number G ≤ k)
    (H : SimpleGraph V) : number H ≤ k :=
  bound_of_adjacent_minimal_compression degreePotential NestedAlongEdges k transfer_edge_card
    hcompression exists_improving_transfer hterminal H

end Erdos184Work.EdgeHull

#print axioms Erdos184Work.Compression.transfer_edge_card
#print axioms Erdos184Work.Compression.transfer_potential_lt
#print axioms Erdos184Work.EdgeHull.bound_of_compression_and_nested

#print axioms Erdos184Work.Compression.NestedAlongEdges.exists_universal
