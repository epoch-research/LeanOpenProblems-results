import Submission.ParityDegreeLower

/-! Parity correction after an adjacent neighborhood transfer. This preserves
certain lower certificates, but does not prove compression monotonicity of the
minimum decomposition number or its hull. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.Compression
set_option maxHeartbeats 300000
variable {V : Type*} [Fintype V]

lemma exists_parity_corrected_transfer (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    ∃ R : SimpleGraph V, R ≤ transfer G u v ∧
      (∀ w : V, Nat.card (R.neighborSet w) % 2 = Nat.card (G.neighborSet w) % 2) ∧
      (∀ w : V, w ≠ v → Nat.card (G.neighborSet w) ≤ Nat.card (R.neighborSet w)) := by
  let T := transfer G u v
  let p := (privateNeighbors G u v).card
  have hu : Nat.card (T.neighborSet u) = Nat.card (G.neighborSet u) + p := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using transfer_degree_left (G := G) huv.ne
  have hv : Nat.card (T.neighborSet v) + p = Nat.card (G.neighborSet v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using transfer_degree_right (G := G) huv.ne
  have ho : ∀ w : V, w ≠ u → w ≠ v → Nat.card (T.neighborSet w) = Nat.card (G.neighborSet w) := by
    intro w hwu hwv
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using transfer_degree_other (G := G) hwu hwv
  by_cases hp : Odd p
  · let R := T.deleteEdges {s(u,v)}
    have ht : T.Adj u v := (transfer_adj_pair G u v).mpr huv
    have hru : Nat.card (R.neighborSet u) + 1 = Nat.card (T.neighborSet u) := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using delete_edge_degree_left ht
    have hrv : Nat.card (R.neighborSet v) + 1 = Nat.card (T.neighborSet v) := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using delete_edge_degree_right ht
    have hro : ∀ w : V, w ≠ u → w ≠ v → Nat.card (R.neighborSet w) = Nat.card (G.neighborSet w) := by
      intro w hwu hwv
      have h := delete_edge_degree_other (G := T) hwu hwv
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h
      exact h.trans (ho w hwu hwv)
    have hp' := Nat.odd_iff.mp hp
    refine ⟨R,T.deleteEdges_le _,?_,?_⟩
    · intro w
      by_cases hwu : w = u
      · subst w
        omega
      by_cases hwv : w = v
      · subst w
        omega
      rw [hro w hwu hwv]
    · intro w hwv
      by_cases hwu : w = u
      · subst w
        omega
      · exact le_of_eq (hro w hwu hwv).symm
  · have hp' : p % 2 = 0 := Nat.not_odd_iff.mp hp
    refine ⟨T,le_rfl,?_,?_⟩
    · intro w
      by_cases hwu : w = u
      · subst w
        omega
      by_cases hwv : w = v
      · subst w
        omega
      rw [ho w hwu hwv]
    · intro w hwv
      by_cases hwu : w = u
      · subst w
        omega
      · exact le_of_eq (ho w hwu hwv).symm

lemma transfer_independent_of_receiver_outside (G : SimpleGraph V) {u v : V}
    (B : Finset V) (huB : u ∉ B) (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y) :
    ∀ x ∈ B, ∀ y ∈ B, ¬ (transfer G u v).Adj x y := by
  intro x hx y hy hxy
  have hxu : x ≠ u := fun h => huB (h ▸ hx)
  have hyu : y ≠ u := fun h => huB (h ▸ hy)
  rcases hxy with hxy | hxy
  · exact hB x hx y hy hxy.1
  · simp only [SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with h | h
    · exact hxu h.1
    · exact hyu h.1

/-- If the sender is outside A and the receiver is outside B, a parity-corrected
transfer preserves an independent-odd certificate and does not decrease the
sum of degrees on A. The sets A and B need not exhaust the vertices. -/
lemma transfer_preserves_subset_certificate (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) (A B O : Finset V) (hvA : v ∉ A) (huB : u ∉ B)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (hoddB : ∀ w ∈ B, Odd (Nat.card (G.neighborSet w)))
    (hoddO : ∀ w ∈ O, Odd (Nat.card (G.neighborSet w))) :
    ∃ R : SimpleGraph V, R ≤ transfer G u v ∧
      (∀ x ∈ B, ∀ y ∈ B, ¬ R.Adj x y) ∧
      (∀ w ∈ B, Odd (Nat.card (R.neighborSet w))) ∧
      (∀ w ∈ O, Odd (Nat.card (R.neighborSet w))) ∧
      (∑ w ∈ A, Nat.card (G.neighborSet w)) ≤ ∑ w ∈ A, Nat.card (R.neighborSet w) := by
  obtain ⟨R,hRT,hpar,hdeg⟩ := exists_parity_corrected_transfer G huv
  refine ⟨R,hRT,?_,?_,?_,?_⟩
  · intro x hx y hy hxy
    exact transfer_independent_of_receiver_outside G B huB hB x hx y hy (hRT hxy)
  · intro w hw
    rw [Nat.odd_iff,hpar w]
    exact Nat.odd_iff.mp (hoddB w hw)
  · intro w hw
    rw [Nat.odd_iff,hpar w]
    exact Nat.odd_iff.mp (hoddO w hw)
  · exact Finset.sum_le_sum (fun w hw => hdeg w (fun h => hvA (h ▸ hw)))

end Erdos184Work.Compression

#print axioms Erdos184Work.Compression.exists_parity_corrected_transfer
#print axioms Erdos184Work.Compression.transfer_preserves_subset_certificate
