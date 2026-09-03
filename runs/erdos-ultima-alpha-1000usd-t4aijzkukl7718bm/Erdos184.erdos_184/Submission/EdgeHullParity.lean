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
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = _ := Finset.sum_congr rfl (fun x _ => (hd x).symm)

lemma transfer_right_independent
    (hno : ∀ x y : B, ¬ G.Adj (.inr x) (.inr y)) :
    ∀ x y : B, ¬ (transfer G (.inl a) (.inr b)).Adj (.inr x) (.inr y) := by
  intro x y hxy
  by_cases hxb : x = b
  · subst x
    by_cases hyb : y = b
    · subst y
      exact (transfer G (.inl a) (.inr b)).loopless _ hxy
    · exact hno _ _ ((transfer_adj_right G (by simp) (by simp)
        (by simpa using hyb)).mp hxy).1
  by_cases hyb : y = b
  · subst y
    exact hno _ _ ((transfer_adj_right G (by simp) (by simp)
      (by simpa using hxb)).mp hxy.symm).1
  exact hno _ _ ((transfer_adj_away G (by simp) (by simpa using hxb)
    (by simp) (by simpa using hyb)).mp hxy)

/-- An odd independent-side certificate survives adjacent compression after,
if necessary, deletion of the joining edge. This does not assert that all
minimal graphs have an independent-side certificate. -/
lemma transfer_preserves_odd_independent_certificate
    (hab : G.Adj (.inl a) (.inr b))
    (hno : ∀ x y : B, ¬ G.Adj (.inr x) (.inr y))
    (hodd : ∀ x : B, Odd (G.degree (.inr x))) :
    ∃ R : SimpleGraph (A ⊕ B), R ≤ transfer G (.inl a) (.inr b) ∧
      (∀ x y : B, ¬ R.Adj (.inr x) (.inr y)) ∧
      (∀ x : B, Odd (R.degree (.inr x))) ∧
      (∑ x : A, G.degree (.inl x)) ≤ ∑ x : A, R.degree (.inl x) := by
  let H := transfer G (.inl a) (.inr b)
  have hHno := transfer_right_independent G a b hno
  have hHab : H.Adj (.inl a) (.inr b) := (transfer_adj_pair G _ _).mpr hab
  have hother : ∀ x : B, x ≠ b → H.degree (.inr x) = G.degree (.inr x) := by
    intro x hxb
    exact transfer_degree_other (by simp) (by simpa using hxb)
  have hsum := transfer_left_sum G a b
  have hdeg := transfer_degree_right (G := G) (u := Sum.inl a) (v := Sum.inr b) (by simp)
  change H.degree (.inr b) + (privateNeighbors G (.inl a) (.inr b)).card = _ at hdeg
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hodd hother hsum hdeg ⊢
  by_cases hb : Odd (Nat.card (H.neighborSet (.inr b)))
  · refine ⟨H,le_rfl,hHno,?_,?_⟩
    · intro x
      by_cases hxb : x = b
      · subst x
        exact hb
      · rw [hother x hxb]
        exact hodd x
    · change _ ≤ ∑ x : A, Nat.card ((transfer G (.inl a) (.inr b)).neighborSet (.inl x))
      rw [hsum]
      omega
  · let R := H.deleteEdges {s(Sum.inl a,Sum.inr b)}
    have hd := delete_edge_degree_right hHab
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd
    change Nat.card (R.neighborSet (.inr b)) + 1 = Nat.card (H.neighborSet (.inr b)) at hd
    have hp : 1 ≤ (privateNeighbors G (.inl a) (.inr b)).card := by
      have ho := hodd b
      rw [Nat.odd_iff] at ho hb
      omega
    refine ⟨R,H.deleteEdges_le _,fun x y hxy => hHno x y ((H.deleteEdges_le _) hxy),?_,?_⟩
    · intro x
      by_cases hxb : x = b
      · subst x
        rw [Nat.odd_iff] at hb ⊢
        omega
      · have hr := delete_edge_degree_other (G := H) (u := Sum.inl a) (v := Sum.inr b)
          (w := Sum.inr x) (by simp) (by simpa using hxb)
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hr
        change Nat.card (R.neighborSet (.inr x)) = Nat.card (H.neighborSet (.inr x)) at hr
        rw [hr,hother x hxb]
        exact hodd x
    · have hs := delete_cross_edge_left_sum H a b hHab
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs
      change (∑ x : A, Nat.card (R.neighborSet (.inl x))) + 1 =
        (∑ x : A, Nat.card (H.neighborSet (.inl x))) at hs
      change (∑ x : A, Nat.card (H.neighborSet (.inl x))) = _ at hsum
      omega

/-- The transferred hull satisfies the original odd-independent-side lower bound.
The conclusion is a lower bound, not an upper bound for decomposition numbers. -/
lemma transfer_hull_parity_lower
    (hab : G.Adj (.inl a) (.inr b))
    (hno : ∀ x y : B, ¬ G.Adj (.inr x) (.inr y))
    (hodd : ∀ x : B, Odd (G.degree (.inr x))) :
    (∑ x : A, G.degree (.inl x)) + 2 * Fintype.card A * Fintype.card B ≤
      2 * Fintype.card A * EdgeHull.value (transfer G (.inl a) (.inr b)) + Fintype.card B := by
  obtain ⟨R,hR,hRno,hRodd,hs⟩ := transfer_preserves_odd_independent_certificate G a b hab hno hodd
  obtain ⟨D,hD,hdec,hcard⟩ := Critical.exists_minimum R
  have ha : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  have hlo := CriticalExample.independent_side_lower_bound R ha hRno hRodd D hD hdec
  rw [hcard] at hlo
  have hn := EdgeHull.le_value hR
  have hm := Nat.mul_le_mul_left (2 * Fintype.card A) hn
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hlo hs hm ⊢
  omega

end Bipartition

end Erdos184Work.Compression

#print axioms Erdos184Work.Compression.transfer_degree_left
#print axioms Erdos184Work.Compression.transfer_degree_right
#print axioms Erdos184Work.Compression.transfer_degree_other

#print axioms Erdos184Work.Compression.transfer_preserves_odd_independent_certificate

#print axioms Erdos184Work.Compression.transfer_hull_parity_lower
