import Submission.Work

/-! A leaf and a degree-two vertex cannot share a neighbor in a smallest
failure. The two deleted vertices are restored by a single path. -/
namespace Erdos583LeafTipSeparationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue Erdos583Work.LeafPairReduction
open scoped Classical
set_option maxHeartbeats 1600000

lemma leaf_tip_common_neighbor_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v a b : Fin n} (huv : u ≠ v)
    (hua : G.Adj u a) (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=a ∨ x=b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {u,v}ᶜ
  have hbu : b ≠ u := by
    intro h
    have h' := hu v (h ▸ hvb.symm)
    exact hva.ne h'
  have haS : a ∈ S := by simp [S,hua.ne.symm,hva.ne.symm]
  have hconn : (G.induce S).Connected := DegreeTwoPacking.induce_dominated_boundary_connected hG {u,v} haS (by
    intro x hx y _ hxy
    rcases hx with hx|hx
    · subst x
      exact Or.inl (hu y hxy)
    · have hx : x=v := hx
      subst x
      rcases hv y hxy with hy|hy
      · exact Or.inl hy
      · subst y; exact Or.inr hab)
  let P : G.Walk u b := .cons hua (.cons hva.symm (.cons hvb .nil))
  have hp : P.IsPath := by
    simp [P,Walk.cons_isPath_iff,hua.ne,huv,hbu.symm,hva.ne.symm,hab.ne,hvb.ne]
  have heq : G.deleteEdges P.toSubgraph.edgeSet=within G S := by
    ext x y
    rw [deleteEdges_adj]
    constructor
    · rintro ⟨hxy,hn⟩
      have hnot (x y : Fin n) (hxy : G.Adj x y) (hn : s(x,y) ∉ P.toSubgraph.edgeSet) : x ∈ S := by
        have hxu : x ≠ u := by
          rintro rfl
          have hy := hu y hxy
          subst y
          exact hn (by simp [P])
        have hxv : x ≠ v := by
          rintro rfl
          rcases hv y hxy with hy|hy
          · subst y; exact hn (by simp [P,Sym2.eq_swap])
          · subst y; exact hn (by simp [P])
        simpa [S] using And.intro hxu hxv
      exact ⟨hxy,hnot x y hxy hn,hnot y x hxy.symm (by simpa only [Sym2.eq_swap] using hn)⟩
    · rintro ⟨hxy,hx,hy⟩
      refine ⟨hxy,?_⟩
      intro he
      have hpE : s(x,y)=s(u,a) ∨ s(x,y)=s(a,v) ∨ s(x,y)=s(v,b) := by
        simpa only [P,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
          List.mem_cons,List.not_mem_nil,or_false] using he
      rcases hpE with he|he|he
      · rcases Sym2.eq_iff.mp he with ⟨rfl,_⟩|⟨_,rfl⟩
        · exact hx (Or.inl rfl)
        · exact hy (Or.inl rfl)
      · rcases Sym2.eq_iff.mp he with ⟨_,rfl⟩|⟨rfl,_⟩
        · exact hy (Or.inr rfl)
        · exact hx (Or.inr rfl)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,_⟩|⟨_,rfl⟩
        · exact hx (Or.inr rfl)
        · exact hy (Or.inr rfl)
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G S (two_removed_lt huv) hconn
  have hex := lift_induce_within S D hD
  rw [←heq] at hex
  obtain ⟨E,hE,hEc⟩ := hex
  obtain ⟨F,hF,hFc⟩ := restore_path_subgraph ⟨u,b,P,hp,rfl⟩ hE
  exact ⟨F,hF,two_removed_budget huv hDc (by omega)⟩

lemma leaf_tip_neighbors_disjoint {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hu : Nat.card (G.neighborSet u)=1) (hv : Nat.card (G.neighborSet v)=2) :
    Disjoint (G.neighborSet u) (G.neighborSet v) := by
  apply Set.disjoint_left.mpr
  intro a hua hva
  obtain ⟨a',hu',hNu⟩ := leaf_data hu
  have haa' : a=a' := hNu a hua
  obtain ⟨b,hvb,hab,hNv⟩ := DegreeTwoPacking.degree_two_triangle_at_neighbor hsmall hG hfail hva hv
  have huv : u ≠ v := by intro h; rw [h,hv] at hu; omega
  exact hfail (leaf_tip_common_neighbor_reduction hsmall hG huv hua hva hvb hab
    (fun x hx ↦ (hNu x hx).trans haa'.symm) hNv)

end Erdos583LeafTipSeparationDevelopment
