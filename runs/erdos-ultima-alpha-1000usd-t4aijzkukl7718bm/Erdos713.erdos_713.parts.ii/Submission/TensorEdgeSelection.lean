import FormalConjecturesUtil
import Submission.ProductCoverObstructions
import Submission.OrientedCloneCount

/-! An extremal-number bound for every H-free spanning edge selection from
a categorical graph product. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713TensorEdgeSelection
open Erdos713ProductCover
variable {V U W : Type*}
set_option maxHeartbeats 1000000

def rectangle (G : SimpleGraph V) (F : SimpleGraph U) (J : SimpleGraph (V × U))
    (v : V) (u : U) : SimpleGraph (F.neighborSet u ⊕ G.neighborSet v) :=
  Erdos713OrientedCloneC8.graph ⊥ (fun x y => J.Adj (v,y.val) (x.val,u))

lemma rectangle_copy (G : SimpleGraph V) (F : SimpleGraph U) (J : SimpleGraph (V × U))
    (v : V) (u : U) : rectangle G F J v u ⊑ J := by
  refine ⟨⟨⟨starRectangle G F v u,?_⟩,(starRectangle G F v u).injective⟩⟩
  rintro (a|a) (b|b) h
  · exact h.elim
  · exact h
  · change J.Adj (v,b.val) (a.val,u) at h
    exact h.symm
  · exact h.elim

lemma rectangle_edges [Fintype V] [Fintype U] (G : SimpleGraph V) (F : SimpleGraph U)
    (J : SimpleGraph (V × U)) (v : V) (u : U) :
    Nat.card (rectangle G F J v u).edgeSet =
      ∑ x : G.neighborSet v, ∑ y : F.neighborSet u, if J.Adj (v,y.val) (x.val,u) then 1 else 0 := by
  have hh := Erdos713OrientedCloneCount.graph_edge_card
    (⊥ : SimpleGraph (F.neighborSet u)) (fun x : G.neighborSet v => fun y => J.Adj (v,y.val) (x.val,u))
  change Nat.card (rectangle G F J v u).edgeSet = _ at hh
  simpa only [edgeSet_bot,Nat.card_eq_fintype_card,Fintype.card_ofIsEmpty,zero_add,
    Fintype.card_subtype,card_filter,Fintype.sum_prod_type] using hh

lemma sum_neighbors [Fintype V] (G : SimpleGraph V) (v : V) (f : V → ℕ) :
    (∑ x : G.neighborSet v, f x.val) = ∑ x : V, if G.Adj v x then f x else 0 := by
  calc
    _ = ∑ x ∈ G.neighborFinset v, f x :=
      (sum_subtype (G.neighborFinset v) (fun x => by simp) f).symm
    _ = _ := by rw [neighborFinset_eq_filter,sum_filter]

lemma rectangle_edges_full [Fintype V] [Fintype U] (G : SimpleGraph V) (F : SimpleGraph U)
    (J : SimpleGraph (V × U)) (hJ : J ≤ tensor G F) (v : V) (u : U) :
    Nat.card (rectangle G F J v u).edgeSet =
      ∑ x : V, ∑ y : U, if J.Adj (v,y) (x,u) then 1 else 0 := by
  rw [rectangle_edges]
  conv_lhs =>
    arg 2; ext x
    rw [sum_neighbors F u (fun y => if J.Adj (v,y) (x.val,u) then 1 else 0)]
  rw [sum_neighbors G v (fun x => ∑ y : U, if F.Adj u y then
    (if J.Adj (v,y) (x,u) then 1 else 0) else 0)]
  apply sum_congr rfl
  intro x _
  by_cases hg : G.Adj v x
  · rw [if_pos hg]
    apply sum_congr rfl
    intro y _
    by_cases hj : J.Adj (v,y) (x,u)
    · have hc := hJ hj
      change G.Adj v x ∧ F.Adj y u at hc
      simp [hj,hc.2.symm]
    · simp [hj]
  · rw [if_neg hg]
    symm
    apply sum_eq_zero
    intro y _
    exact if_neg (fun hj => hg (hJ hj).1)

/-- Every retained product edge belongs to exactly two crossed-star
rectangles. The proof counts ordered edges rather than quotient edges. -/
lemma sum_rectangle_edges [Fintype V] [Fintype U] (G : SimpleGraph V) (F : SimpleGraph U)
    (J : SimpleGraph (V × U)) (hJ : J ≤ tensor G F) :
    (∑ v : V, ∑ u : U, Nat.card (rectangle G F J v u).edgeSet) = 2*Nat.card J.edgeSet := by
  simp_rw [rectangle_edges_full G F J hJ]
  have hh := J.two_mul_card_edgeFinset
  simp only [card_filter,Fintype.sum_prod_type,edgeFinset_card,← Nat.card_eq_fintype_card] at hh
  rw [hh]
  apply sum_congr rfl
  intro v _
  rw [sum_comm (f := fun u : U => fun x : V => ∑ y : U, if J.Adj (v,y) (x,u) then 1 else 0)]
  conv_lhs => arg 2; ext x; rw [sum_comm]
  rw [sum_comm]

/-- Neither factor needs to be H-free. Only the retained subgraph is
assumed H-free. Small rectangle orders are handled by their actual
extremal numbers, without a monotonicity assumption. -/
theorem edge_bound [Fintype V] [Fintype U] (H : SimpleGraph W) (G : SimpleGraph V)
    (F : SimpleGraph U) (J : SimpleGraph (V × U)) (hJ : J ≤ tensor G F) (hf : H.Free J) :
    2*Nat.card J.edgeSet ≤ ∑ v : V, ∑ u : U,
      extremalNumber (Nat.card (F.neighborSet u)+Nat.card (G.neighborSet v)) H := by
  rw [← sum_rectangle_edges G F J hJ]
  apply sum_le_sum
  intro v _
  apply sum_le_sum
  intro u _
  have hr : H.Free (rectangle G F J v u) := fun h => hf (h.trans (rectangle_copy G F J v u))
  have hh := card_edgeFinset_le_extremalNumber hr
  simpa only [edgeFinset_card,Nat.card_eq_fintype_card,Fintype.card_sum] using hh

#print axioms rectangle_copy
#print axioms sum_rectangle_edges
#print axioms edge_bound
end Erdos713TensorEdgeSelection
