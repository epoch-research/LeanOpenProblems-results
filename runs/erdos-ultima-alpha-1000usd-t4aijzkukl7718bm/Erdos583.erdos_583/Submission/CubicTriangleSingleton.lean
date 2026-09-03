import Submission.OneMemberReplacement

/-! Restoring a cubic triangle pair when its external edge is a singleton member. -/
namespace Erdos583CubicTriangleSingletonDevelopment
open SimpleGraph Erdos583Work
open Erdos583OneMemberReplacementDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma cubic_triangle_singleton_lift {V : Type*} {G : SimpleGraph V} {r x y a b : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b) (hab : G.Adj a b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (D : Finset (puncture G ({x,y} : Set V)).Subgraph)
    (hD : GoodDecomposition (puncture G ({x,y} : Set V)) D)
    (K : (puncture G ({x,y} : Set V)).Subgraph) (hKD : K ∈ D) (hKe : K.edgeSet={s(a,b)}) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let S : Set V := {x,y}
  let H := puncture G S
  let A : G.Walk r y := Walk.cons hrx (Walk.cons hxa (Walk.cons hab (Walk.cons hyb.symm Walk.nil)))
  let B : G.Walk r x := Walk.cons hry (Walk.cons hxy.symm Walk.nil)
  have hA : A.IsPath := by
    apply Walk.IsPath.mk'
    simp [A,Walk.support,hrx.ne,har.symm,hbr.symm,hry.ne,hxa.ne,hbx.symm,hxy.ne,hab.ne,hay,hyb.ne.symm]
  have hB : B.IsPath := by simp [B,Walk.cons_isPath_iff,hry.ne,hrx.ne,hxy.ne.symm]
  have hAB : Disjoint A.toSubgraph.edgeSet B.toSubgraph.edgeSet := by
    simp [Set.disjoint_left,A,B,hrx.ne,hrx.ne.symm,hry.ne,hry.ne.symm,hxy.ne,hxy.ne.symm,
      hxa.ne.symm,hyb.ne,hyb.ne.symm,har,hay,hbr,hbx]
  have hAc : Disjoint A.toSubgraph.edgeSet (H.edgeSet \ K.edgeSet) := by
    rw [hKe]
    apply Set.disjoint_left.mpr
    intro e he hh
    simp only [A,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hh.1.2.2 (Or.inl rfl)
    · exact hh.1.2.1 (Or.inl rfl)
    · exact hh.2 rfl
    · exact hh.1.2.2 (Or.inr rfl)
  have hBc : Disjoint B.toSubgraph.edgeSet (H.edgeSet \ K.edgeSet) := by
    apply Set.disjoint_left.mpr
    intro e he hh
    simp only [B,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact hh.1.2.2 (Or.inr rfl)
    · exact hh.1.2.1 (Or.inr rfl)
  have hcov : G.edgeSet=(H.edgeSet ∪ A.toSubgraph.edgeSet) ∪ B.toSubgraph.edgeSet := by
    apply puncture_two_walks_cover S A B
    intro t ht z htz
    rcases ht with rfl | rfl
    · rcases hNx z htz with rfl | rfl | rfl <;> simp [A,B,Sym2.eq_swap]
    · rcases hNy z htz with rfl | rfl | rfl <;> simp [A,B,Sym2.eq_swap]
  have hcover : G.edgeSet=((H.edgeSet \ K.edgeSet) ∪ A.toSubgraph.edgeSet) ∪ B.toSubgraph.edgeSet := by
    rw [hcov,hKe]
    have he : s(a,b) ∈ A.toSubgraph.edgeSet := by simp [A]
    ext e
    simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
    constructor
    · rintro ((h|h)|h)
      · by_cases heq : e=s(a,b)
        · exact Or.inl (Or.inr (heq ▸ he))
        · exact Or.inl (Or.inl ⟨h,heq⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · tauto
  exact replace_one_by_two (puncture_le G S) D hD K hKD A.toSubgraph B.toSubgraph
    ⟨_,_,A,hA,rfl⟩ ⟨_,_,B,hB,rfl⟩ hAB hAc hBc hcover

end Erdos583CubicTriangleSingletonDevelopment
