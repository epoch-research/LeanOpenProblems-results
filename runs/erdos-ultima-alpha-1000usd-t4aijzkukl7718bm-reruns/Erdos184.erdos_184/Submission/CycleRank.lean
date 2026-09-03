import Submission.Cycles

/-! A cycle-space bound for edge-disjoint cycle decompositions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma cycle_has_edge_outside_forest {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : SimpleGraph V) (ht : T.IsAcyclic) (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    (H.edgeSet \ T.edgeSet).Nonempty := by
  by_contra hn
  have hsub : H.edgeSet ⊆ T.edgeSet := by
    intro e he
    by_contra heT
    exact hn ⟨e, he, heT⟩
  let f : H.coe →g T := ⟨Subtype.val, fun {x y} h =>
    hsub (show s(x.val, y.val) ∈ H.edgeSet from h)⟩
  have ha : H.coe.IsAcyclic := ht.comap f Subtype.val_injective
  have he : ∀ v, Even (H.coe.degree v) := fun v => by rw [hr v]; decide
  have hb := even_acyclic_eq_bot H.coe (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using he) ha
  obtain ⟨v⟩ := hc.nonempty
  have hd := hr v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd
  simp [hb] at hd

lemma cycle_decomposition_forest_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (T : SimpleGraph V) (ht : T.IsAcyclic) (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : D.card ≤ (G.edgeFinset \ T.edgeFinset).card := by
  have hex : ∀ H : {H // H ∈ D}, ∃ e : Sym2 V, e ∈ H.val.edgeSet ∧ e ∉ T.edgeSet := by
    intro H
    exact cycle_has_edge_outside_forest T ht H.val (hcy H.val H.property).1
      (hcy H.val H.property).2
  choose f hf using hex
  let g : {H // H ∈ D} → {e // e ∈ G.edgeFinset \ T.edgeFinset} :=
    fun H => ⟨f H, by
      simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
      exact ⟨H.val.edgeSet_subset (hf H).1, (hf H).2⟩⟩
  have hg : Function.Injective g := by
    intro H K h
    have hef : f H = f K := congrArg Subtype.val h
    apply Subtype.ext
    by_contra hHK
    exact Set.disjoint_left.mp (hd.1 H.property K.property hHK) (hf H).1
      (hef.symm ▸ (hf K).1)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg

lemma connected_cycle_decomposition_rank_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hc : G.Connected) (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    D.card + Fintype.card V ≤ G.edgeFinset.card + 1 := by
  obtain ⟨T, hTG, ht⟩ := hc.exists_isTree_le
  have hbound := cycle_decomposition_forest_bound G T ht.IsAcyclic D hcy hd
  have hsub : T.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (SimpleGraph.edgeSet_mono hTG (SimpleGraph.mem_edgeFinset.mp he))
  have hcardle := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hsub] at hbound
  have hcard := ht.card_edgeFinset
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hbound hcard hcardle ⊢
  omega

end Erdos184
