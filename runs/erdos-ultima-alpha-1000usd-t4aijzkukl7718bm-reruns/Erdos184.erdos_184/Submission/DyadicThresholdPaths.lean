import Submission.LogDeficitPaths

/-! Deletion thresholds depending on the deletion cost, not on the ambient order. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.LogDeficit
set_option maxHeartbeats 1000000

/-- Once a dyadic scale pays the deletion cost, every larger scale does too. -/
lemma threshold_persists {j t : ℕ} (hj : 1 ≤ j)
    (ht : 4*(j+1)*(j+2)*t ≤ 2^j) {x : ℕ} (hx : 2^j ≤ x) :
    4*scale x*t ≤ x := by
  have hp (k : ℕ) (hk : j ≤ k) : 4*(k+1)*(k+2)*t ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => exact ht
    | @succ k hk ih =>
      have hquad : (k+2)*(k+3) ≤ 2*(k+1)*(k+2) := by nlinarith
      have hmul := Nat.mul_le_mul_right (4*t) hquad
      simp only [pow_succ]
      nlinarith
  have hjlog := Nat.le_log_of_pow_le (by decide : 1 < 2) hx
  have hpos : x ≠ 0 := by
    have hpow := Nat.two_pow_pos j
    omega
  have hl := hp (Nat.log 2 x) hjlog
  have hxpow := Nat.pow_log_le_self 2 hpos
  unfold scale
  nlinarith

end Erdos184.LogDeficit

namespace Erdos184.ExpansionPaths
open SqrtDeficitSeparator (externalBoundary)
variable {V : Type*} [Fintype V]

/-- Attach an expanding-neighborhood path to the two prescribed endpoints,
then erase repetitions. No disjointness of the two neighborhoods is needed. -/
lemma short_path_of_large_degrees (H : SimpleGraph V) {a R : ℕ} (hR : 0 < R)
    (hexp : ExpandsAbove H a R) (u v : V)
    (hu : 0 < H.degree u) (hau : a ≤ H.degree u)
    (hv : 0 < H.degree v) (hav : a ≤ H.degree v) :
    ∃ p : H.Walk u v, p.IsPath ∧
      p.length ≤ 2*R*(Nat.log 2 (Fintype.card V)+1)+2 := by
  have cardN (w : V) : (H.neighborSet w).ncard = H.degree w := by
    rw [Set.ncard_eq_toFinset_card']
    exact H.card_neighborFinset_eq_degree w
  obtain ⟨b,hb,c,hc,p,hp,hlen⟩ := short_path_between_sets H hR hexp
    (H.neighborSet u) (H.neighborSet v)
    (by rwa [cardN]) (by rwa [cardN]) (by rwa [cardN]) (by rwa [cardN])
  let q := (p.append hc.symm.toWalk).cons hb
  refine ⟨q.bypass,q.bypass_isPath,q.length_bypass_le.trans ?_⟩
  have hq : q.length = p.length+2 := by simp [q]
  omega

/-- Deleting F edges can remove at most |F| neighbors at any fixed vertex. -/
lemma degree_le_deleteEdges_add (G : SimpleGraph V) (F : Set (Sym2 V)) (v : V) :
    G.degree v ≤ (G.deleteEdges F).degree v + F.ncard := by
  let A := G.neighborSet v \ (G.deleteEdges F).neighborSet v
  have hmap : (fun u => s(v,u)) '' A ⊆ F := by
    rintro _ ⟨u,hu,rfl⟩
    by_contra hn
    exact hu.2 (SimpleGraph.deleteEdges_adj.mpr ⟨hu.1,hn⟩)
  have hinj : Set.InjOn (fun u => s(v,u)) A := by
    intro a _ b _ hab
    rcases Sym2.eq_iff.mp hab with h | h
    · exact h.2
    · exact h.2.trans h.1
  have hcard : A.ncard ≤ F.ncard := by
    rw [← Set.ncard_image_of_injOn hinj]
    exact Set.ncard_le_ncard hmap
  have hsub : (G.deleteEdges F).neighborSet v ⊆ G.neighborSet v := fun _ h => h.1
  have heq := Set.ncard_diff_add_ncard_of_subset hsub
  have cardN (H : SimpleGraph V) : (H.neighborSet v).ncard = H.degree v := by
    rw [Set.ncard_eq_toFinset_card']
    exact H.card_neighborFinset_eq_degree v
  rw [cardN,cardN] at heq
  dsimp only [A] at hcard
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at heq ⊢
  omega

end Erdos184.ExpansionPaths

namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit ExpansionPaths
open SqrtDeficitSeparator (externalBoundary)
universe u
variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}

lemma IsVertexMinimal.expands_after_edges_at_scale (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t j : ℕ) (hF : F.ncard ≤ C*t)
    (hj : 1 ≤ j) (ht : 4*(j+1)*(j+2)*t ≤ 2^j) :
    ExpandsAbove (G.deleteEdges F) (2^j) (12*scale (Fintype.card V)) := by
  intro X hlow hX hhalf
  have hm := scale_mono (show X.ncard ≤ Fintype.card V by omega)
  have hb := hG.robust_boundary_bound hC F t hF X hX hhalf
    (threshold_persists hj ht hlow)
  exact hb.le.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hm))

lemma IsVertexMinimal.expands_after_packing_at_scale (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (t j : ℕ) (hP : P.card ≤ C*t) (hj : 1 ≤ j)
    (ht : 4*(j+1)*(j+2)*t ≤ 2^j) :
    ExpandsAbove (G \ unionPieces G P) (2^j) (12*scale (Fintype.card V)) := by
  intro X hlow hX hhalf
  have hm := scale_mono (show X.ncard ≤ Fintype.card V by omega)
  have hb := hG.robust_packing_boundary_bound hC P hc hd t hP X hX hhalf
    (threshold_persists hj ht hlow)
  exact hb.le.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hm))

/-- The set-size threshold 2^j is independent of |V|. -/
lemma IsVertexMinimal.short_path_after_edges_at_scale (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t j : ℕ) (hF : F.ncard ≤ C*t)
    (hj : 1 ≤ j) (ht : 4*(j+1)*(j+2)*t ≤ 2^j)
    (A B : Set V) (haA : 2^j ≤ A.ncard) (haB : 2^j ≤ B.ncard) :
    ∃ u ∈ A, ∃ v ∈ B, ∃ p : (G.deleteEdges F).Walk u v,
      p.IsPath ∧ p.length ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1) := by
  have hp : 0 < 2^j := Nat.two_pow_pos j
  obtain ⟨u,hu,v,hv,p,hp,hlen⟩ := short_path_between_sets (G.deleteEdges F)
    (show 0 < 12*scale (Fintype.card V) from Nat.mul_pos (by decide) (scale_pos _))
    (hG.expands_after_edges_at_scale hC F t j hF hj ht) A B
    (hp.trans_le haA) haA (hp.trans_le haB) haB
  exact ⟨u,hu,v,hv,p,hp,by nlinarith⟩

/-- For C>=512, deleting at most C arbitrary edges preserves polylogarithmic
paths between prescribed vertices, not just between large endpoint sets. -/
lemma IsVertexMinimal.short_path_after_small_edge_deletion (hG : IsVertexMinimal C G)
    (hC : 512 ≤ C) (F : Set (Sym2 V)) (hF : F.ncard ≤ C) (u v : V) :
    ∃ p : (G.deleteEdges F).Walk u v, p.IsPath ∧
      p.length ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1)+2 := by
  have hC0 : 0 < C := by omega
  have hd (w : V) : 512 ≤ (G.deleteEdges F).degree w := by
    have hdeg := hG.degree_lower hC0 w
    have hdel := degree_le_deleteEdges_add G F w
    omega
  obtain ⟨p,hp,hlen⟩ := short_path_of_large_degrees (G.deleteEdges F)
    (show 0 < 12*scale (Fintype.card V) from Nat.mul_pos (by decide) (scale_pos _))
    (hG.expands_after_edges_at_scale hC0 F 1 9 (by simpa using hF) (by decide) (by decide))
    u v
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (show 0 < (G.deleteEdges F).degree u from (by decide : 0 < 512).trans_le (hd u)))
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hd u)
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (show 0 < (G.deleteEdges F).degree v from (by decide : 0 < 512).trans_le (hd v)))
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hd v)
  exact ⟨p,hp,by nlinarith⟩

end Erdos184.LogDeficitSeparator
