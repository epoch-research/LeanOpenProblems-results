import Submission.ParityCorrectedTransfer

/-! Preservation of disjoint independent-odd lower certificates in the
arbitrary-edge hull under adjacent transfers. This is not a compression
inequality for the minimum decomposition number of an arbitrary graph. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work
set_option maxHeartbeats 400000

namespace EdgeHull
open Critical
variable {V W : Type*} [Fintype V] [Fintype W]

lemma value_le_of_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    value G ≤ value H := by
  apply (value_le_iff G (value H)).mpr
  intro R hRG
  let T := R.map e.toEquiv.toEmbedding
  have hTH : T ≤ H := by
    intro x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
    exact e.toHom.map_adj (hRG hab)
  have hn := BlockRestriction.number_eq_of_iso (SimpleGraph.Iso.map e.toEquiv R)
  exact hn.le.trans (le_value hTH)

lemma value_eq_of_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    value G = value H :=
  le_antisymm (value_le_of_iso e) (value_le_of_iso e.symm)

end EdgeHull

namespace Compression
variable {V : Type*} [Fintype V]

lemma transfer_swap_adj (G : SimpleGraph V) {u v : V} (huv : u ≠ v) (x y : V) :
    (transfer G u v).Adj x y ↔
      (transfer G v u).Adj (Equiv.swap u v x) (Equiv.swap u v y) := by
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hxu : x = u
  · subst x
    by_cases hyv : y = v
    · subst y
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, transfer_adj_pair]
      exact G.adj_comm u v
    · have hyu : y ≠ u := Ne.symm hxy
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyu hyv,
        transfer_adj_left G huv hyu hyv, transfer_adj_left G huv.symm hyv hyu]
      exact or_comm
  by_cases hxv : x = v
  · subst x
    by_cases hyu : y = u
    · subst y
      simp only [Equiv.swap_apply_left,Equiv.swap_apply_right]
      rw [(transfer G u v).adj_comm v u,transfer_adj_pair,
        (transfer G v u).adj_comm u v,transfer_adj_pair]
      exact G.adj_comm u v
    · have hyv : y ≠ v := Ne.symm hxy
      rw [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne hyu hyv,
        transfer_adj_right G huv hyu hyv,transfer_adj_right G huv.symm hyv hyu]
      exact and_comm
  by_cases hyu : y = u
  · subst y
    rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hxu hxv,
      (transfer G u v).adj_comm x u,transfer_adj_left G huv hxu hxv,
      (transfer G v u).adj_comm x v,
      transfer_adj_left G huv.symm hxv hxu]
    exact or_comm
  by_cases hyv : y = v
  · subst y
    rw [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne hxu hxv,
      (transfer G u v).adj_comm x v,transfer_adj_right G huv hxu hxv,
      (transfer G v u).adj_comm x u,
      transfer_adj_right G huv.symm hxv hxu]
    exact and_comm
  rw [Equiv.swap_apply_of_ne_of_ne hxu hxv,Equiv.swap_apply_of_ne_of_ne hyu hyv,
    transfer_adj_away G hxu hxv hyu hyv,transfer_adj_away G hxv hxu hyv hyu]

noncomputable def transferSwapIso (G : SimpleGraph V) {u v : V} (huv : u ≠ v) :
    transfer G u v ≃g transfer G v u where
  toEquiv := Equiv.swap u v
  map_rel_iff' := by
    intro x y
    exact (transfer_swap_adj G huv x y).symm

lemma transfer_value_swap (G : SimpleGraph V) {u v : V} (huv : u ≠ v) :
    EdgeHull.value (transfer G u v) = EdgeHull.value (transfer G v u) :=
  EdgeHull.value_eq_of_iso (transferSwapIso G huv)

lemma transfer_degree_sum_of_mem (G : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (A : Finset V) (huA : u ∈ A) (hvA : v ∈ A) :
    (∑ w ∈ A, Nat.card ((transfer G u v).neighborSet w)) =
      ∑ w ∈ A, Nat.card (G.neighborSet w) := by
  have hs := sum_exchange_two
    (fun w => if w ∈ A then Nat.card ((transfer G u v).neighborSet w) else 0)
    (fun w => if w ∈ A then Nat.card (G.neighborSet w) else 0) huv (by
      intro w hwu hwv
      by_cases hw : w ∈ A
      · simp only [if_pos hw]
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using transfer_degree_other (G := G) hwu hwv
      · simp only [if_neg hw])
  simp only [if_pos huA,if_pos hvA] at hs
  simp only [Finset.sum_ite_mem,Finset.univ_inter] at hs
  have hl := transfer_degree_left (G := G) huv
  have hr := transfer_degree_right (G := G) huv
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hl hr
  omega

lemma transfer_preserves_internal_certificate (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) (A B O : Finset V) (huA : u ∈ A) (hvA : v ∈ A)
    (hAB : Disjoint A B) (hAO : Disjoint A O)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (hoddB : ∀ w ∈ B, Odd (Nat.card (G.neighborSet w)))
    (hoddO : ∀ w ∈ O, Odd (Nat.card (G.neighborSet w))) :
    (∀ x ∈ B, ∀ y ∈ B, ¬ (transfer G u v).Adj x y) ∧
      (∀ w ∈ B, Odd (Nat.card ((transfer G u v).neighborSet w))) ∧
      (∀ w ∈ O, Odd (Nat.card ((transfer G u v).neighborSet w))) ∧
      (∑ w ∈ A, Nat.card (G.neighborSet w)) ≤
        ∑ w ∈ A, Nat.card ((transfer G u v).neighborSet w) := by
  have huB : u ∉ B := fun h => Finset.disjoint_left.mp hAB huA h
  refine ⟨transfer_independent_of_receiver_outside G B huB hB,?_,?_,?_⟩
  · intro w hw
    have hwu : w ≠ u := fun h => huB (h ▸ hw)
    have hwv : w ≠ v := fun h => Finset.disjoint_left.mp hAB hvA (h ▸ hw)
    have he := transfer_degree_other (G := G) hwu hwv
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he
    rw [he]
    exact hoddB w hw
  · intro w hw
    have hwu : w ≠ u := fun h => Finset.disjoint_left.mp hAO huA (h ▸ hw)
    have hwv : w ≠ v := fun h => Finset.disjoint_left.mp hAO hvA (h ▸ hw)
    have he := transfer_degree_other (G := G) hwu hwv
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he
    rw [he]
    exact hoddO w hw
  · exact le_of_eq (transfer_degree_sum_of_mem G huv.ne A huA hvA).symm

/-- An admissible orientation preserves the certificate in a subgraph of the
transfer. Either the sender is outside A, or both endpoints are inside A. -/
lemma transfer_certificate_oriented (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) (A B O : Finset V) (huB : u ∉ B)
    (hdir : v ∉ A ∨ u ∈ A ∧ v ∈ A)
    (hAB : Disjoint A B) (hAO : Disjoint A O)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (hoddB : ∀ w ∈ B, Odd (Nat.card (G.neighborSet w)))
    (hoddO : ∀ w ∈ O, Odd (Nat.card (G.neighborSet w))) :
    ∃ R : SimpleGraph V, R ≤ transfer G u v ∧
      (∀ x ∈ B, ∀ y ∈ B, ¬ R.Adj x y) ∧
      (∀ w ∈ B, Odd (Nat.card (R.neighborSet w))) ∧
      (∀ w ∈ O, Odd (Nat.card (R.neighborSet w))) ∧
      (∑ w ∈ A, Nat.card (G.neighborSet w)) ≤ ∑ w ∈ A, Nat.card (R.neighborSet w) := by
  rcases hdir with hvA | ⟨huA,hvA⟩
  · exact transfer_preserves_subset_certificate G huv A B O hvA huB hB hoddB hoddO
  · exact ⟨_,le_rfl,transfer_preserves_internal_certificate G huv A B O huA hvA
      hAB hAO hB hoddB hoddO⟩

lemma transfer_certificate_oriented_bound (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) (A B O : Finset V) (hA : 1 ≤ A.card) (huB : u ∉ B)
    (hdir : v ∉ A ∨ u ∈ A ∧ v ∈ A)
    (hAB : Disjoint A B) (hAO : Disjoint A O)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (hoddB : ∀ w ∈ B, Odd (Nat.card (G.neighborSet w)))
    (hoddO : ∀ w ∈ O, Odd (Nat.card (G.neighborSet w))) :
    (∑ w ∈ A, Nat.card (G.neighborSet w)) + (2 * A.card - 2) * B.card + O.card ≤
      2 * A.card * EdgeHull.value (transfer G u v) := by
  obtain ⟨R,hRT,hRB,hRoB,hRoO,hsum⟩ := transfer_certificate_oriented G huv A B O
    huB hdir hAB hAO hB hoddB hoddO
  obtain ⟨D,hD,hdec,hcard⟩ := Critical.exists_minimum R
  have hb := ParityDegreeLower.independent_odd_degree_bound D hD hdec A B O hA hAO hRB
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hRoB)
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hRoO)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hb
  rw [hcard] at hb
  have hh := Nat.mul_le_mul_left (2 * A.card) (EdgeHull.le_value hRT)
  omega

/-- Enhanced parity certificates with A disjoint from the odd independent set
survive every adjacent transfer, after choosing the appropriate orientation.
Opposite orientations are isomorphic, so the resulting bound holds for the
specified transfer. No certificate-completeness hypothesis is asserted. -/
lemma transfer_certificate_bound (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) (A B O : Finset V) (hA : 1 ≤ A.card)
    (hAB : Disjoint A B) (hAO : Disjoint A O)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (hoddB : ∀ w ∈ B, Odd (Nat.card (G.neighborSet w)))
    (hoddO : ∀ w ∈ O, Odd (Nat.card (G.neighborSet w))) :
    (∑ w ∈ A, Nat.card (G.neighborSet w)) + (2 * A.card - 2) * B.card + O.card ≤
      2 * A.card * EdgeHull.value (transfer G u v) := by
  by_cases huB : u ∈ B
  · have hvB : v ∉ B := fun hvB => hB u huB v hvB huv
    have huA : u ∉ A := fun huA => Finset.disjoint_left.mp hAB huA huB
    rw [transfer_value_swap G huv.ne]
    exact transfer_certificate_oriented_bound G huv.symm A B O hA hvB
      (Or.inl huA) hAB hAO hB hoddB hoddO
  · by_cases hvA : v ∈ A
    · by_cases huA : u ∈ A
      · exact transfer_certificate_oriented_bound G huv A B O hA huB
          (Or.inr ⟨huA,hvA⟩) hAB hAO hB hoddB hoddO
      · have hvB : v ∉ B := fun hvB => Finset.disjoint_left.mp hAB hvA hvB
        rw [transfer_value_swap G huv.ne]
        exact transfer_certificate_oriented_bound G huv.symm A B O hA hvB
          (Or.inl huA) hAB hAO hB hoddB hoddO
    · exact transfer_certificate_oriented_bound G huv A B O hA huB
        (Or.inl hvA) hAB hAO hB hoddB hoddO

/-- A certificate crossing the preceding integer threshold proves the desired
hull bound for this graph and edge. Its existence is an explicit hypothesis. -/
lemma transfer_hull_ge_of_certificate (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) (A B O : Finset V) (hA : 1 ≤ A.card)
    (hAB : Disjoint A B) (hAO : Disjoint A O)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (hoddB : ∀ w ∈ B, Odd (Nat.card (G.neighborSet w)))
    (hoddO : ∀ w ∈ O, Odd (Nat.card (G.neighborSet w)))
    (k : ℕ)
    (hcert : 2 * A.card * (k - 1) <
      (∑ w ∈ A, Nat.card (G.neighborSet w)) + (2 * A.card - 2) * B.card + O.card) :
    k ≤ EdgeHull.value (transfer G u v) := by
  have hbound := transfer_certificate_bound G huv A B O hA hAB hAO hB hoddB hoddO
  by_contra hk
  have hle : EdgeHull.value (transfer G u v) ≤ k - 1 := by omega
  have hmul := Nat.mul_le_mul_left (2 * A.card) hle
  omega

end Compression
end Erdos184Work

#print axioms Erdos184Work.EdgeHull.value_eq_of_iso
#print axioms Erdos184Work.Compression.transferSwapIso
#print axioms Erdos184Work.Compression.transfer_degree_sum_of_mem
#print axioms Erdos184Work.Compression.transfer_preserves_internal_certificate

#print axioms Erdos184Work.Compression.transfer_certificate_bound

#print axioms Erdos184Work.Compression.transfer_hull_ge_of_certificate
