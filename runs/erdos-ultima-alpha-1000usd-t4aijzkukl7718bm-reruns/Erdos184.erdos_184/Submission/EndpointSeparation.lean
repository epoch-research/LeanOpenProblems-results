import Submission.ShiftThreeDegreePairs

/-!
Endpoint-only resilience yields larger common-cycle packings. These are
necessary conditions on critical graphs, not a proof of the conjecture.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace EndpointSeparation
open ExactVertexSmoothing
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

/-- Only the degrees of the two separated vertices enter this extraction. -/
lemma induce_compl_reachable_of_endpoint_degrees (G : SimpleGraph V) (S : Set V)
    (u w : ↥(Sᶜ)) (hdu : 4 ≤ G.degree u.val) (hdw : 4 ≤ G.degree w.val)
    (hno : ∀ A B : SimpleGraph V, A ≤ G → B ≤ G →
      Disjoint A.edgeSet B.edgeSet → A.edgeSet ∪ B.edgeSet = G.edgeSet →
      A.support ∩ B.support ⊆ S →
      4 ≤ A.support.ncard → 4 ≤ B.support.ncard →
      A.support.ncard < Fintype.card V → B.support.ncard < Fintype.card V → False)
    : (G.induce Sᶜ).Reachable u w := by
  by_contra hn
  let R := G.induce Sᶜ
  let T : Set V := {x | x ∈ S ∨ ∃ hx : x ∈ Sᶜ, R.Reachable u ⟨x,hx⟩}
  let A := RankBlocks.sideGraph G T
  let B := G \ A
  have hA : A ≤ G := fun _ _ h => h.1
  have hB : B ≤ G := sdiff_le
  have huT : u.val ∈ T := Or.inr ⟨u.property,Reachable.refl _⟩
  have hwT : w.val ∉ T := by
    rintro (h | ⟨hx,h⟩)
    · exact w.property h
    · exact hn h
  have hclosed {x y : V} (hx : x ∈ T) (hxS : x ∉ S)
      (hxy : G.Adj x y) : y ∈ T := by
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    obtain ⟨hx',hux⟩ := hx.resolve_left hxS
    have hRxy : R.Adj ⟨x,hx'⟩ ⟨y,hyS⟩ := hxy
    exact Or.inr ⟨hyS,hux.trans hRxy.reachable⟩
  have hdis : Disjoint A.edgeSet B.edgeSet := by
    change Disjoint A.edgeSet (G \ A).edgeSet
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet := by
    change A.edgeSet ∪ (G \ A).edgeSet = G.edgeSet
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hA)
  have hinter : A.support ∩ B.support ⊆ S := by
    rintro x ⟨⟨y,hy⟩,⟨z,hz⟩⟩
    by_contra hxS
    exact hz.2 ⟨hz.1,hy.2.1,hclosed hy.2.1 hxS hz.1⟩
  have hwA : w.val ∉ A.support := by
    rintro ⟨x,hx⟩
    exact hwT hx.2.1
  have huB : u.val ∉ B.support := by
    rintro ⟨x,hx⟩
    exact hx.2 ⟨hx.1,huT,hclosed huT u.property hx.1⟩
  have hAl : A.support.ncard < Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      using Fintype.card_subtype_lt hwA
  have hBl : B.support.ncard < Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      using Fintype.card_subtype_lt huB
  have hnu : G.neighborSet u.val ⊆ A.support := by
    intro x hx
    have hux : A.Adj u.val x := ⟨hx,huT,hclosed huT u.property hx⟩
    exact ⟨u.val,hux.symm⟩
  have hnw : G.neighborSet w.val ⊆ B.support := by
    intro x hx
    have hwx : B.Adj w.val x := ⟨hx,fun h => hwT h.2.1⟩
    exact ⟨w.val,hwx.symm⟩
  have hduA : G.degree u.val ≤ A.support.ncard := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using Set.ncard_le_ncard hnu
  have hdwB : G.degree w.val ≤ B.support.ncard := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using Set.ncard_le_ncard hnw
  exact hno A B hA hB hdis hcover hinter
    (by omega) (by omega) hAl hBl


/-- In an even graph the adjacent case needs no connectivity assumption.
For nonadjacent endpoints only endpoint-to-endpoint Menger connectivity is used. -/
lemma cycle_through_pair_of_even {G : SimpleGraph V} (he : ∀ x, Even (G.degree x))
    {u v : V} (huv : u ≠ v)
    (hconn : ∀ S : Set V, S.ncard ≤ 1 → (hu : u ∉ S) → (hv : v ∉ S) →
      (G.induce Sᶜ).Reachable ⟨u,hu⟩ ⟨v,hv⟩) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      u ∈ H.verts ∧ v ∈ H.verts := by
  by_cases hadj : G.Adj u v
  · obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G he
    have heG : s(u,v) ∈ G.edgeSet := hadj
    rw [← hd.2] at heG
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp heG
    have hHuv : H.Adj u v := H.mem_edgeSet.mp heH
    exact ⟨H,hc H hH,H.edge_vert hHuv,H.edge_vert hHuv.symm⟩
  · obtain ⟨p,hp,hd,hs⟩ := MengerMatching.exists_internally_disjoint_paths (k := 2) huv hadj
      (by intro S hS huS hvS; exact hconn S (by omega) huS hvS)
    let P := p 0
    let Q := (p 1).reverse
    have hPQ : P.edges.Disjoint Q.edges := by
      simpa only [P,Q,Walk.edges_reverse,List.disjoint_reverse_right] using hd 0 1 (by decide)
    have hi : ∀ x, x ∈ P.support → x ∈ Q.support → x = u ∨ x = v := by
      intro x hx hy
      exact hs 0 1 (by decide) x hx (by simpa only [Q,Walk.support_reverse,List.mem_reverse] using hy)
    have hc := TwoTerminalGluing.append_isCycle_of_paths P Q (hp 0) (hp 1).reverse huv hPQ hi
    refine ⟨(P.append Q).toSubgraph,cycle_subgraph_regular G hc,?_,?_⟩
    · exact (P.append Q).mem_verts_toSubgraph.mpr (P.append Q).start_mem_support
    · exact (P.append Q).mem_verts_toSubgraph.mpr
        (Walk.subset_support_append_left P Q P.end_mem_support)

end EndpointSeparation
end Erdos184
