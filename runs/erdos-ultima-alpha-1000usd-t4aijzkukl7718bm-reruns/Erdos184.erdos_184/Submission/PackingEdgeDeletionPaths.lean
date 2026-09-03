import Submission.DyadicThresholdPaths

/-! Short paths after simultaneous cycle-packing and edge deletions.
The remainder is not asserted to be minimal or count-critical. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.ExpansionPaths
open SqrtDeficitSeparator (externalBoundary)
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma ExpandsAbove.mono {H K : SimpleGraph V} {a R : ℕ}
    (hH : ExpandsAbove H a R) (hHK : H ≤ K) : ExpandsAbove K a R := by
  intro X ha hpos hhalf
  have hs : externalBoundary H X ⊆ externalBoundary K X := by
    rintro v ⟨hv,u,hu,huv⟩
    exact ⟨hv,u,hu,hHK huv⟩
  exact (hH X ha hpos hhalf).trans
    (Nat.mul_le_mul_left R (Set.ncard_le_ncard hs))

omit [Fintype V] in
lemma unionPieces_mono_set {G : SimpleGraph V} {P Q : Finset G.Subgraph} (hPQ : P ⊆ Q) :
    unionPieces G P ≤ unionPieces G Q := by
  intro x y hxy
  change s(x,y) ∈ (unionPieces G P).edgeSet at hxy
  change s(x,y) ∈ (unionPieces G Q).edgeSet
  rw [unionPieces_edgeSet] at hxy ⊢
  obtain ⟨H,hHP,he⟩ := Set.mem_iUnion₂.mp hxy
  exact Set.mem_iUnion₂.mpr ⟨H,hPQ hHP,he⟩

/-- Extend an existing packing by at most |F| pieces so that its remainder
avoids all F edges as well. The added pieces may be arbitrarily long. -/
lemma extend_packing_to_avoid_edges (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (F : Set (Sym2 V)) :
    ∃ Q : Finset G.Subgraph,
      (∀ H ∈ Q, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (Q : Set G.Subgraph) (fun H => H.edgeSet) ∧
      P ⊆ Q ∧ Q.card ≤ P.card+F.ncard ∧
      G \ unionPieces G Q ≤ (G \ unionPieces G P).deleteEdges F := by
  obtain ⟨E,hcE,hdE⟩ := even_cycle_decomposition (G \ unionPieces G P) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing G he P hc hd v)
  obtain ⟨D,hcD,hdD,hPD,_⟩ := complete_cycle_packing_extension G P hc hd E (by
    intro H hH
    refine ⟨(hcE H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcE H hH).2 v) hdE
  obtain ⟨S,hSD,hSF,havoid⟩ := ShiftedCritical.exists_packing_cover_edges D hdD F
  let Q := P ∪ S
  have hQD : Q ⊆ D := Finset.union_subset hPD hSD
  have hPQ : P ⊆ Q := Finset.subset_union_left
  have hSQ : S ⊆ Q := Finset.subset_union_right
  have hpq := unionPieces_mono_set hPQ
  have hsq := unionPieces_mono_set hSQ
  refine ⟨Q,fun H hH => hcD H (hQD hH),
    fun H hH K hK hne => hdD.1 (hQD hH) (hQD hK) hne,hPQ,?_,?_⟩
  · exact (Finset.card_union_le P S).trans (Nat.add_le_add_left hSF P.card)
  · intro x y hxy
    have hS : (G \ unionPieces G S).Adj x y := ⟨hxy.1,fun h => hxy.2 (hsq h)⟩
    have heF := SimpleGraph.deleteEdges_adj.mp (havoid hS)
    exact SimpleGraph.deleteEdges_adj.mpr
      ⟨⟨hxy.1,fun h => hxy.2 (hpq h)⟩,heF.2⟩

end Erdos184.ExpansionPaths

namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit ExpansionPaths
universe u
variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}

lemma IsVertexMinimal.expands_after_packing_edges_at_scale (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (F : Set (Sym2 V)) (t j : ℕ) (hcost : P.card+F.ncard ≤ C*t)
    (hj : 1 ≤ j) (ht : 4*(j+1)*(j+2)*t ≤ 2^j) :
    ExpandsAbove ((G \ unionPieces G P).deleteEdges F) (2^j)
      (12*scale (Fintype.card V)) := by
  obtain ⟨Q,hcQ,hdQ,_,hcard,hres⟩ := extend_packing_to_avoid_edges G hG.1 P hc hd F
  exact (hG.expands_after_packing_at_scale hC Q hcQ hdQ t j
    (hcard.trans hcost) hj ht).mono hres

/-- Explicit sufficient budgets for retaining short paths between fixed
vertices after both sorts of deletion. -/
lemma IsVertexMinimal.short_path_after_packing_edges (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (F : Set (Sym2 V)) (hcost : P.card+F.ncard ≤ C)
    (hdegree : 2*P.card+F.ncard+512 ≤ 2*(C+2)) (u v : V) :
    ∃ p : ((G \ unionPieces G P).deleteEdges F).Walk u v, p.IsPath ∧
      p.length ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1)+2 := by
  let R := G \ unionPieces G P
  let H := R.deleteEdges F
  have hdeg (w : V) : 512 ≤ H.degree w := by
    have hGv := hG.degree_lower hC w
    have hPv := ShiftedCritical.packing_degree_le P hc hd w
    have hr := degree_sdiff_of_le (unionPieces_le G P) w
    have hf := degree_le_deleteEdges_add R F w
    simp only [R,H,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hGv hPv hr hf ⊢
    omega
  have hexp : ExpandsAbove H (2^9) (12*scale (Fintype.card V)) :=
    hG.expands_after_packing_edges_at_scale hC P hc hd F 1 9
      (by simpa using hcost) (by decide) (by decide)
  obtain ⟨p,hp,hlen⟩ := short_path_of_large_degrees H
    (show 0 < 12*scale (Fintype.card V) from Nat.mul_pos (by decide) (scale_pos _))
    hexp u v
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (show 0 < H.degree u from (by decide : 0 < 512).trans_le (hdeg u)))
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hdeg u)
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (show 0 < H.degree v from (by decide : 0 < 512).trans_le (hdeg v)))
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hdeg v)
  exact ⟨p,hp,by nlinarith⟩

end Erdos184.LogDeficitSeparator
