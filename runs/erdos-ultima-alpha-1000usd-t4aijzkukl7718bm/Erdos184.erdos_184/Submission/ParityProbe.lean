import Submission.EdgeHullParityBase

/-! Odd independent-side certificates under adjacent neighborhood transfer.
This does not assert that all minimal graphs have such a certificate. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.Compression
set_option maxHeartbeats 100000

section Bipartition
variable {A B : Type*} [Fintype A] [Fintype B]
noncomputable local instance : DecidableEq (A ⊕ B) := Classical.decEq _
variable (G : SimpleGraph (A ⊕ B)) (a : A) (b : B)

lemma transfer_left_sum :
    (∑ x : A, (transfer G (.inl a) (.inr b)).degree (.inl x)) =
      (∑ x : A, G.degree (.inl x)) + (privateNeighbors G (.inl a) (.inr b)).card := by
  have hd : ∀ x : A,
      (transfer G (.inl a) (.inr b)).degree (.inl x) = G.degree (.inl x) +
        if x = a then (privateNeighbors G (.inl a) (.inr b)).card else 0 := by
    intro x
    by_cases hxa : x = a
    · subst x
      simpa only [ite_true,eq_self] using transfer_degree_left (G := G) (u := .inl a)
        (v := .inr b) (by simp)
    · rw [if_neg hxa,add_zero]
      exact transfer_degree_other (by simpa using hxa) (by simp)
  simp only [hd,Finset.sum_add_distrib]
  simp

lemma delete_cross_edge_left_sum (hab : G.Adj (.inl a) (.inr b)) :
    (∑ x : A, (G.deleteEdges {s(Sum.inl a,Sum.inr b)}).degree (.inl x)) + 1 =
      ∑ x : A, G.degree (.inl x) := by
  have hd : ∀ x : A, G.degree (.inl x) =
      (G.deleteEdges {s(Sum.inl a,Sum.inr b)}).degree (.inl x) + if x = a then 1 else 0 := by
    intro x
    by_cases hxa : x = a
    · subst x
      simpa using (delete_edge_degree_left hab).symm
    · rw [if_neg hxa,add_zero]
      exact (delete_edge_degree_other (G := G) (by simpa using hxa) (by simp)).symm
  calc
    _ = ∑ x : A, ((G.deleteEdges {s(Sum.inl a,Sum.inr b)}).degree (.inl x) +
        if x = a then 1 else 0) := by
      trace_state
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = _ := Finset.sum_congr rfl (fun x _ => (hd x).symm)


end Bipartition
end Erdos184Work.Compression
