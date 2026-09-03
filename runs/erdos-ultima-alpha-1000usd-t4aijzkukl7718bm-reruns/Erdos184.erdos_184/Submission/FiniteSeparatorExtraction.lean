import Submission.ThreeVertexSeparation

/-! Separator extraction with a parameterized lower bound on side sizes. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.FiniteTerminalGluing
variable {V : Type*} [Fintype V]

set_option maxHeartbeats 800000 in
/-- Extract the two proper side supports from failure of reachability after
vertex deletion. Degree at least d makes both side supports have size at least d. -/
lemma induce_compl_reachable_of_endpoint_degrees (G : SimpleGraph V) (S : Set V) (d : ℕ)
    (u w : ↥(Sᶜ)) (hdegree_u : d ≤ G.degree u.val) (hdegree_w : d ≤ G.degree w.val)
    (hno : ∀ A B : SimpleGraph V, A ≤ G → B ≤ G →
      Disjoint A.edgeSet B.edgeSet → A.edgeSet ∪ B.edgeSet = G.edgeSet →
      A.support ∩ B.support ⊆ S →
      d ≤ A.support.ncard → d ≤ B.support.ncard →
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
  have hdu : G.degree u.val ≤ A.support.ncard := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using Set.ncard_le_ncard hnu
  have hdw : G.degree w.val ≤ B.support.ncard := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using Set.ncard_le_ncard hnw
  exact hno A B hA hB hdis hcover hinter
    (by omega) (by omega) hAl hBl

/-- The uniform-degree version of the endpoint extraction. -/
lemma induce_compl_reachable_of_no_split (G : SimpleGraph V) (S : Set V) (d : ℕ)
    (hdegree : ∀ x, d ≤ G.degree x)
    (hno : ∀ A B : SimpleGraph V, A ≤ G → B ≤ G →
      Disjoint A.edgeSet B.edgeSet → A.edgeSet ∪ B.edgeSet = G.edgeSet →
      A.support ∩ B.support ⊆ S →
      d ≤ A.support.ncard → d ≤ B.support.ncard →
      A.support.ncard < Fintype.card V → B.support.ncard < Fintype.card V → False)
    (u w : ↥(Sᶜ)) : (G.induce Sᶜ).Reachable u w :=
  induce_compl_reachable_of_endpoint_degrees G S d u w
    (hdegree u.val) (hdegree w.val) hno

end Erdos184.FiniteTerminalGluing
