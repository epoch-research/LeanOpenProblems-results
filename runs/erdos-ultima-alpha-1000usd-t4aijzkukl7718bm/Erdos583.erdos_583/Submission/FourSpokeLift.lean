import Submission.GeneralTwoSpokeLift

/-! A fresh four-spoke vertex can be restored with one extra path when two
of its neighbors have endpoints in distinct receiving slots. -/
namespace Erdos583FourSpokeLiftDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583GeneralTwoSpokeLiftDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

lemma lift_four_spokes {V : Type*} [Fintype V] {G : SimpleGraph V} {r : V} {k : ℕ}
    (a b c d : ({r}ᶜ : Set V)) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : G.Adj r a.val) (hb : G.Adj r b.val) (hc : G.Adj r c.val) (hd : G.Adj r d.val)
    (hN : ∀ x, G.Adj r x → x=a.val ∨ x=b.val ∨ x=c.val ∨ x=d.val)
    (T : TrailFamily (G.induce ({r}ᶜ : Set V)) k) (hp : ∀ i, (T.walk i).IsPath)
    (i j : Fin k) (hij : i ≠ j) (hi : a=T.start i ∨ a=T.finish i)
    (hj : b=T.start j ∨ b=T.finish j) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k+1 := by
  classical
  obtain ⟨R,hR,hia,hjb⟩ := orient_two_slots T hp i j hij a b hi hj
  let P : G.Walk c.val d.val := .cons hc.symm (.cons hd .nil)
  have hP : P.IsPath := by
    have hcd' : c.val ≠ d.val := fun h ↦ hcd (Subtype.ext h)
    simp [P,Walk.isPath_def,hcd',hc.ne.symm,hd.ne]
  let K := G.deleteEdges P.toSubgraph.edgeSet
  have hKG : K.induce ({r}ᶜ : Set V)=G.induce ({r}ᶜ : Set V) := by
    ext x y
    change (G.deleteEdges P.toSubgraph.edgeSet).Adj x.val y.val ↔ G.Adj x.val y.val
    rw [deleteEdges_adj]
    constructor
    · exact And.left
    · intro h
      refine ⟨h,?_⟩
      simp only [Walk.mem_edges_toSubgraph,P,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
        List.not_mem_nil,or_false,Sym2.eq_iff]
      have hx : x.val ≠ r := x.property
      have hy : y.val ≠ r := y.property
      tauto
  have spoke (x : ({r}ᶜ : Set V)) (hx : G.Adj r x.val) (hxc : x ≠ c) (hxd : x ≠ d) :
      K.Adj r x.val := by
    refine deleteEdges_adj.mpr ⟨hx,?_⟩
    simp only [Walk.mem_edges_toSubgraph,P,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Sym2.eq_iff]
    have hxc' : x.val ≠ c.val := fun h ↦ hxc (Subtype.ext h)
    have hxd' : x.val ≠ d.val := fun h ↦ hxd (Subtype.ext h)
    have hxr := hx.ne
    have hrc := hc.ne
    have hrd := hd.ne
    tauto
  have hNc : ¬K.Adj r c.val := by
    intro hh
    apply (deleteEdges_adj.mp hh).2
    exact P.mem_edges_toSubgraph.mpr (by simp [P,Sym2.eq_swap])
  have hNd : ¬K.Adj r d.val := by
    intro hh
    apply (deleteEdges_adj.mp hh).2
    exact P.mem_edges_toSubgraph.mpr (by simp [P])
  have hNK : ∀ x, K.Adj r x → x=a.val ∨ x=b.val := by
    intro x hx
    rcases hN x hx.1 with h|h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hNc (h ▸ hx)).elim
    · exact (hNd (h ▸ hx)).elim
  have hex : ∃ U : TrailFamily (K.induce ({r}ᶜ : Set V)) k,
      (∀ l, (U.walk l).IsPath) ∧ U.start i=a ∧ U.start j=b := by
    rw [hKG]
    exact ⟨R,hR,hia,hjb⟩
  obtain ⟨U,hU,hUi,hUj⟩ := hex
  obtain ⟨D,hD,hDc⟩ := lift_two_spokes_at_distinct_slots (G := K) a b hab
    (spoke a ha hac had) (spoke b hb hbc hbd) hNK U hU i j hij hUi hUj
  obtain ⟨E,hE,hEc⟩ := restore_path_subgraph (show IsPathSubgraph P.toSubgraph from ⟨_,_,P,hP,rfl⟩) hD
  exact ⟨E,hE,by omega⟩

end Erdos583FourSpokeLiftDevelopment
